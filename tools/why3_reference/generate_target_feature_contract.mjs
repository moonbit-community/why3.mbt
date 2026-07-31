#!/usr/bin/env node
// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import {
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, '..', '..');
const WHY3_COMMIT = '1343338d3bb1941c0d4f134283bb0790816113c4';
const WHY3_TREE = 'f5e82693620413d7d8e3ebcba69addcb6a65f877';
const WHY3_ARCHIVE_SHA256 =
  'c7bf782933a5d8ef9e78638cbf18e480eef895dca95317ba50231f20d45e92c7';
const PROJECT_AST_INVENTORY_PATH = join(
  PROJECT_ROOT,
  'tools',
  'contracts',
  'parser-ast-inventory-v1.json',
);
const FULL_MLW_PATCH_PATH = join(
  SCRIPT_DIRECTORY,
  'patches',
  'full-mlw-export.patch',
);

function fail(message) {
  throw new Error(message);
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex');
}

function canonicalSha(value) {
  return sha256(`${JSON.stringify(value)}\n`);
}

function compareUtf8(left, right) {
  return Buffer.compare(Buffer.from(left, 'utf8'), Buffer.from(right, 'utf8'));
}

function runChecked(command, argv, options = {}) {
  const result = spawnSync(command, argv, {
    cwd: options.cwd ?? PROJECT_ROOT,
    encoding: 'utf8',
    env: { ...process.env, LC_ALL: 'C', LANG: 'C', TZ: 'UTC' },
    maxBuffer: 128 * 1024 * 1024,
    shell: false,
  });
  if (result.status !== 0 || result.signal !== null ||
      (result.error && result.error.code !== 'EPERM')) {
    const detail =
      `${result.stdout ?? ''}${result.stderr ?? ''}${result.error?.message ?? ''}`.trim();
    fail(`${command} ${argv.join(' ')} failed: ${detail}`);
  }
  return result.stdout ?? '';
}

function parseArguments(argv) {
  const result = {
    why3Root: resolve(PROJECT_ROOT, '..', 'why3'),
    why3Archive: null,
    mode: 'stdout',
    path: null,
  };
  let explicitRoot = false;
  for (let index = 0; index < argv.length; index += 1) {
    const option = argv[index];
    if (![
      '--why3-root',
      '--why3-archive',
      '--output',
      '--check',
    ].includes(option)) {
      fail(`unknown argument ${option}`);
    }
    const value = argv[index + 1];
    if (value === undefined) fail(`${option} requires a path`);
    if (option === '--why3-root') {
      result.why3Root = resolve(value);
      explicitRoot = true;
    } else if (option === '--why3-archive') {
      result.why3Archive = resolve(value);
    } else {
      if (result.mode !== 'stdout') {
        fail('--output and --check are mutually exclusive');
      }
      result.mode = option.slice(2);
      result.path = resolve(value);
    }
    index += 1;
  }
  if (explicitRoot && result.why3Archive !== null) {
    fail('--why3-root and --why3-archive are mutually exclusive');
  }
  return result;
}

function maskOcamlComments(source, path) {
  let output = '';
  let depth = 0;
  let inString = false;
  let escaped = false;
  for (let index = 0; index < source.length; index += 1) {
    const current = source[index];
    const next = source[index + 1];
    if (depth > 0) {
      if (current === '(' && next === '*') {
        depth += 1;
        output += '  ';
        index += 1;
      } else if (current === '*' && next === ')') {
        depth -= 1;
        output += '  ';
        index += 1;
      } else {
        output += current === '\n' ? '\n' : ' ';
      }
      continue;
    }
    if (inString) {
      output += current;
      if (escaped) escaped = false;
      else if (current === '\\') escaped = true;
      else if (current === '"') inString = false;
      continue;
    }
    if (current === '(' && next === '*') {
      depth = 1;
      output += '  ';
      index += 1;
    } else {
      output += current;
      if (current === '"') inString = true;
    }
  }
  if (depth !== 0) fail(`unterminated OCaml comment in ${path}`);
  if (inString) fail(`unterminated OCaml string in ${path}`);
  return output;
}

function escapeRegExp(value) {
  return value.replace(/[.*+?^${}()|[\]\\]/gu, '\\$&');
}

function typeBody(masked, typeName, path) {
  const declaration = new RegExp(
    `^(?:type|and)\\s+(?:'[a-z][A-Za-z0-9_']*\\s+)*` +
    `${escapeRegExp(typeName)}\\b[^=\\n]*=\\s*(?:private\\s+)?`,
    'mu',
  );
  const match = declaration.exec(masked);
  if (match === null) fail(`${path} has no type ${typeName}`);
  const start = match.index + match[0].length;
  const tail = masked.slice(start);
  const next = /^(?:type|and|module|val|exception|class)\b/gmu.exec(tail);
  return tail.slice(0, next?.index ?? tail.length);
}

function extractConstructors(masked, typeName, path) {
  const body = typeBody(masked, typeName, path);
  return [...body.matchAll(/(?:^|\|)\s*([A-Z][A-Za-z0-9_']*)\b/gu)]
    .map(match => match[1]);
}

function extractRecordFields(masked, typeName, path) {
  const body = typeBody(masked, typeName, path);
  const start = body.indexOf('{');
  const end = body.indexOf('}', start + 1);
  if (start < 0 || end < 0) fail(`${path} type ${typeName} is not a record`);
  return [...body.slice(start + 1, end).matchAll(
    /^\s*([a-z][A-Za-z0-9_']*)\s*:/gmu,
  )].map(match => match[1]);
}

function assertEqual(actual, expected, label) {
  if (JSON.stringify(actual) !== JSON.stringify(expected)) {
    fail(
      `${label} drift: expected ${JSON.stringify(expected)}, ` +
      `got ${JSON.stringify(actual)}`,
    );
  }
}

function words(value) {
  const trimmed = value.trim();
  return trimmed === '' ? [] : trimmed.split(/\s+/u);
}

const VARIANT_FAMILIES = [
  ['src/util/number.mli', 'Number', 'int_literal_kind',
    'ILitUnk ILitDec ILitHex ILitOct ILitBin', 'literal', 2],
  ['src/util/number.mli', 'Number', 'real_literal_kind',
    'RLitUnk RLitDec RLitHex', 'literal', 2],
  ['src/util/constant.mli', 'Constant', 'constant',
    'ConstInt ConstReal ConstStr', 'literal', 2],

  ['src/parser/ptree.ml', 'Ptree', 'attr',
    'ATstr ATpos', 'surface-ast', 1],
  ['src/parser/ptree.ml', 'Ptree', 'qualid',
    'Qident Qdot', 'surface-ast', 1],
  ['src/parser/ptree.ml', 'Ptree', 'pty',
    'PTtyvar PTtyapp PTtuple PTref PTarrow PTscope PTparen PTpure',
    'surface-ast', 1],
  ['src/parser/ptree.ml', 'Ptree', 'pat_desc',
    'Pwild Pvar Papp Prec Ptuple Pas Por Pcast Pscope Pparen Pghost',
    'surface-ast', 1],
  ['src/parser/ptree.ml', 'Ptree', 'term_desc',
    'Ttrue Tfalse Tconst Tident Tasref Tidapp Tapply Tinfix Tinnfix ' +
    'Tbinop Tbinnop Tnot Tif Tquant Teps Tattr Tlet Tcase Tcast Ttuple ' +
    'Trecord Tupdate Tscope Tat',
    'surface-ast', 1],
  ['src/parser/ptree.ml', 'Ptree', 'expr_desc',
    'Eref Etrue Efalse Econst Eident Easref Eidapp Eapply Einfix Einnfix ' +
    'Elet Erec Efun Eany Etuple Erecord Eupdate Eassign Esequence Eif ' +
    'Ewhile Eand Eor Enot Ematch Eabsurd Epure Eidpur Eraise Eexn ' +
    'Eoptexn Efor Eassert Escope Elabel Ecast Eghost Eattr',
    'surface-ast', 1],
  ['src/parser/ptree.ml', 'Ptree', 'type_def',
    'TDalias TDalgebraic TDrecord TDrange TDfloat', 'surface-ast', 1],
  ['src/parser/ptree.ml', 'Ptree', 'visibility',
    'Public Private Abstract', 'surface-ast', 1],
  ['src/parser/ptree.ml', 'Ptree', 'metarg',
    'Mty Mfs Mps Max Mlm Mgl Mval Mstr Mint', 'surface-ast', 1],
  ['src/parser/ptree.ml', 'Ptree', 'clone_subst',
    'CStsym CSfsym CSpsym CSvsym CSxsym CSprop CSaxiom CSlemma CSgoal',
    'surface-ast', 1],
  ['src/parser/ptree.ml', 'Ptree', 'decl',
    'Dtype Dlogic Dind Dprop Dlet Drec Dexn Dmeta Dcloneexport Duseexport ' +
    'Dcloneimport Duseimport Dimport Dscope',
    'surface-ast', 1],
  ['src/parser/ptree.ml', 'Ptree', 'mlw_file',
    'Modules Decls', 'surface-ast', 1],

  ['src/core/dterm.mli', 'Dterm', 'dpattern_node',
    'DPwild DPvar DPapp DPor DPas DPcast', 'logic-typing-ir', 2],
  ['src/core/dterm.mli', 'Dterm', 'dbinop',
    'DTand DTand_asym DTor DTor_asym DTimplies DTiff DTby DTso',
    'logic-typing-ir', 2],
  ['src/core/dterm.mli', 'Dterm', 'dquant',
    'DTforall DTexists DTlambda', 'logic-typing-ir', 2],
  ['src/core/dterm.mli', 'Dterm', 'dterm_node',
    'DTvar DTgvar DTconst DTapp DTfapp DTif DTlet DTcase DTeps DTquant ' +
    'DTbinop DTnot DTtrue DTfalse DTcast DTuloc DTattr',
    'logic-typing-ir', 2],

  ['src/mlw/dexpr.mli', 'Dexpr', 'dpattern_node',
    'DPwild DPvar DPapp DPas DPor DPcast', 'program-typing-ir', 5],
  ['src/mlw/dexpr.mli', 'Dexpr', 'dxsymbol',
    'DElexn DEgexn', 'program-typing-ir', 5],
  ['src/mlw/dexpr.mli', 'Dexpr', 'dexpr_node',
    'DEvar DEsym DEconst DEapp DEfun DEany DElet DErec DEnot DEand DEor ' +
    'DEif DEmatch DEassign DEwhile DEfor DEraise DEghost DEexn DEoptexn ' +
    'DEassert DEpure DEvar_pure DEls_pure DEpv_pure DEabsurd DEtrue ' +
    'DEfalse DElabel DEcast DEuloc DEattr',
    'program-typing-ir', 5],

  ['src/core/ty.mli', 'Ty', 'type_def',
    'NoDef Alias Range Float', 'core-graph', 2],
  ['src/core/ty.mli', 'Ty', 'ty_node',
    'Tyvar Tyapp', 'core-graph', 2],
  ['src/core/term.mli', 'Term', 'pattern_node',
    'Pwild Pvar Papp Por Pas', 'core-graph', 2],
  ['src/core/term.mli', 'Term', 'quant',
    'Tforall Texists', 'core-graph', 2],
  ['src/core/term.mli', 'Term', 'binop',
    'Tand Tor Timplies Tiff', 'core-graph', 2],
  ['src/core/term.mli', 'Term', 'term_node',
    'Tvar Tconst Tapp Tif Tlet Tcase Teps Tquant Tbinop Tnot Ttrue Tfalse',
    'core-graph', 2],
  ['src/core/decl.mli', 'Decl', 'ind_sign',
    'Ind Coind', 'core-graph', 2],
  ['src/core/decl.mli', 'Decl', 'prop_kind',
    'Plemma Paxiom Pgoal', 'core-graph', 2],
  ['src/core/decl.mli', 'Decl', 'decl_node',
    'Dtype Ddata Dparam Dlogic Dind Dprop', 'core-graph', 2],
  ['src/core/ident.mli', 'Ident', 'notation',
    'SNword SNinfix SNtight SNprefix SNget SNset SNupdate SNcut SNlcut SNrcut',
    'core-identity', 2],
  ['src/core/theory.mli', 'Theory', 'meta_arg_type',
    'MTty MTtysymbol MTlsymbol MTprsymbol MTstring MTint MTid',
    'core-graph', 2],
  ['src/core/theory.mli', 'Theory', 'meta_arg',
    'MAty MAts MAls MApr MAstr MAint MAid', 'core-graph', 2],
  ['src/core/theory.mli', 'Theory', 'tdecl_node',
    'Decl Use Clone Meta', 'core-graph', 2],

  ['src/mlw/ity.mli', 'Ity', 'ity_node',
    'Ityreg Ityapp Ityvar', 'mlw-type-graph', 3],
  ['src/mlw/ity.mli', 'Ity', 'mask',
    'MaskVisible MaskTuple MaskGhost', 'mlw-type-graph', 3],
  ['src/mlw/ity.mli', 'Ity', 'oneway',
    'Total Partial Diverges', 'mlw-type-graph', 3],
  ['src/mlw/expr.mli', 'Expr', 'rs_logic',
    'RLnone RLpv RLls RLlemma', 'mlw-expression-graph', 3],
  ['src/mlw/expr.mli', 'Expr', 'rs_kind',
    'RKnone RKlocal RKfunc RKpred RKlemma', 'mlw-expression-graph', 3],
  ['src/mlw/expr.mli', 'Expr', 'pat_ghost',
    'PGfail PGlast PGnone', 'mlw-expression-graph', 3],
  ['src/mlw/expr.mli', 'Expr', 'pre_pattern',
    'PPwild PPvar PPapp PPas PPor', 'mlw-expression-graph', 3],
  ['src/mlw/expr.mli', 'Expr', 'assertion_kind',
    'Assert Assume Check', 'mlw-expression-graph', 3],
  ['src/mlw/expr.mli', 'Expr', 'for_direction',
    'To DownTo', 'mlw-expression-graph', 3],
  ['src/mlw/expr.mli', 'Expr', 'expr_node',
    'Evar Econst Eexec Eassign Elet Eif Ematch Ewhile Efor Eraise Eexn ' +
    'Eassert Eghost Epure Eabsurd',
    'mlw-expression-graph', 3],
  ['src/mlw/expr.mli', 'Expr', 'cexp_node',
    'Capp Cpur Cfun Cany', 'mlw-expression-graph', 3],
  ['src/mlw/expr.mli', 'Expr', 'let_defn',
    'LDvar LDsym LDrec', 'mlw-expression-graph', 3],
  ['src/mlw/pdecl.mli', 'Pdecl', 'pdecl_node',
    'PDtype PDlet PDexn PDpure', 'mlw-declaration-graph', 3],
  ['src/mlw/pmodule.mli', 'Pmodule', 'prog_symbol',
    'PV RS OO', 'mlw-module-graph', 4],
  ['src/mlw/pmodule.mli', 'Pmodule', 'overload',
    'FixedRes SameType NoOver', 'mlw-module-graph', 4],
  ['src/mlw/pmodule.mli', 'Pmodule', 'mod_unit',
    'Udecl Uuse Uclone Umeta Uscope', 'mlw-module-graph', 4],
].map(([source, owner, type, constructors, layer, migrationPhase]) => ({
  source,
  owner,
  type,
  constructors: words(constructors),
  layer,
  migrationPhase,
}));

function record(
  source,
  owner,
  type,
  rawFields,
  canonicalFields,
  excluded = {},
  layer,
  migrationPhase,
) {
  return {
    source,
    owner,
    type,
    rawFields: words(rawFields),
    canonicalFields: words(canonicalFields),
    excluded,
    layer,
    migrationPhase,
  };
}

const RECORD_FAMILIES = [
  record('src/util/number.mli', 'Number', 'int_constant',
    'il_kind il_int', 'il_kind il_int', {}, 'literal', 2),
  record('src/util/number.mli', 'Number', 'real_value',
    'rv_sig rv_pow2 rv_pow5', 'rv_sig rv_pow2 rv_pow5', {}, 'literal', 2),
  record('src/util/number.mli', 'Number', 'real_constant',
    'rl_kind rl_real', 'rl_kind rl_real', {}, 'literal', 2),
  record('src/parser/ptree.ml', 'Ptree', 'ident',
    'id_str id_ats id_loc', 'id_str id_ats id_loc', {}, 'surface-ast', 1),
  record('src/parser/ptree.ml', 'Ptree', 'pattern',
    'pat_desc pat_loc', 'pat_desc pat_loc', {}, 'surface-ast', 1),
  record('src/parser/ptree.ml', 'Ptree', 'term',
    'term_desc term_loc', 'term_desc term_loc', {}, 'surface-ast', 1),
  record('src/parser/ptree.ml', 'Ptree', 'spec',
    'sp_pre sp_post sp_xpost sp_reads sp_writes sp_alias sp_variant ' +
    'sp_checkrw sp_diverge sp_partial',
    'sp_pre sp_post sp_xpost sp_reads sp_writes sp_alias sp_variant ' +
    'sp_checkrw sp_diverge sp_partial',
    {}, 'surface-ast', 1),
  record('src/parser/ptree.ml', 'Ptree', 'expr',
    'expr_desc expr_loc', 'expr_desc expr_loc', {}, 'surface-ast', 1),
  record('src/parser/ptree.ml', 'Ptree', 'field',
    'f_loc f_ident f_pty f_mutable f_ghost',
    'f_loc f_ident f_pty f_mutable f_ghost', {}, 'surface-ast', 1),
  record('src/parser/ptree.ml', 'Ptree', 'type_decl',
    'td_loc td_ident td_params td_vis td_mut td_inv td_wit td_def',
    'td_loc td_ident td_params td_vis td_mut td_inv td_wit td_def',
    {}, 'surface-ast', 1),
  record('src/parser/ptree.ml', 'Ptree', 'logic_decl',
    'ld_loc ld_ident ld_params ld_type ld_def',
    'ld_loc ld_ident ld_params ld_type ld_def', {}, 'surface-ast', 1),
  record('src/parser/ptree.ml', 'Ptree', 'ind_decl',
    'in_loc in_ident in_params in_def',
    'in_loc in_ident in_params in_def', {}, 'surface-ast', 1),

  record('src/core/dterm.mli', 'Dterm', 'dpattern',
    'dp_node dp_dty dp_vars dp_loc',
    'dp_node dp_dty dp_vars dp_loc', {}, 'logic-typing-ir', 2),
  record('src/core/dterm.mli', 'Dterm', 'dterm',
    'dt_node dt_dty dt_loc',
    'dt_node dt_dty dt_loc', {}, 'logic-typing-ir', 2),
  record('src/mlw/dexpr.mli', 'Dexpr', 'dpattern',
    'dp_pat dp_dity dp_vars dp_loc',
    'dp_pat dp_dity dp_vars dp_loc', {}, 'program-typing-ir', 5),
  record('src/mlw/dexpr.mli', 'Dexpr', 'dspec_final',
    'ds_pre ds_post ds_xpost ds_reads ds_writes ds_diverge ds_partial ds_checkrw',
    'ds_pre ds_post ds_xpost ds_reads ds_writes ds_diverge ds_partial ds_checkrw',
    {}, 'program-typing-ir', 5),
  record('src/mlw/dexpr.mli', 'Dexpr', 'dexpr',
    'de_node de_dvty de_loc',
    'de_node de_dvty de_loc', {}, 'program-typing-ir', 5),
  record('src/mlw/dexpr.mli', 'Dexpr', 'drec_defn',
    'fds', 'fds', {}, 'program-typing-ir', 5),

  record('src/core/ty.mli', 'Ty', 'tvsymbol',
    'tv_name', 'tv_name', {}, 'core-graph', 2),
  record('src/core/ident.mli', 'Ident', 'attribute',
    'attr_string attr_tag', 'attr_string',
    { attr_tag: 'runtime attribute registration tag' }, 'core-identity', 2),
  record('src/core/ident.mli', 'Ident', 'ident',
    'id_string id_attrs id_loc id_tag',
    'id_string id_attrs id_loc',
    { id_tag: 'runtime weak-table tag' }, 'core-identity', 2),
  record('src/core/ident.mli', 'Ident', 'preid',
    'pre_name pre_attrs pre_loc',
    'pre_name pre_attrs pre_loc', {}, 'core-identity', 2),
  record('src/core/ty.mli', 'Ty', 'tysymbol',
    'ts_name ts_args ts_def', 'ts_name ts_args ts_def', {}, 'core-graph', 2),
  record('src/core/ty.mli', 'Ty', 'ty',
    'ty_node ty_tag', 'ty_node',
    { ty_tag: 'runtime weak-table tag' }, 'core-graph', 2),
  record('src/core/term.mli', 'Term', 'vsymbol',
    'vs_name vs_ty', 'vs_name vs_ty', {}, 'core-graph', 2),
  record('src/core/term.mli', 'Term', 'lsymbol',
    'ls_name ls_args ls_value ls_constr ls_proj',
    'ls_name ls_args ls_value ls_constr ls_proj', {}, 'core-graph', 2),
  record('src/core/term.mli', 'Term', 'pattern',
    'pat_node pat_vars pat_ty', 'pat_node pat_ty',
    { pat_vars: 'derived bound-variable cache' }, 'core-graph', 2),
  record('src/core/term.mli', 'Term', 'term',
    't_node t_ty t_attrs t_loc',
    't_node t_ty t_attrs t_loc', {}, 'core-graph', 2),
  record('src/core/decl.mli', 'Decl', 'prsymbol',
    'pr_name', 'pr_name', {}, 'core-graph', 2),
  record('src/core/decl.mli', 'Decl', 'decl',
    'd_node d_news d_tag', 'd_node',
    {
      d_news: 'derived introduced-identifier cache',
      d_tag: 'runtime weak-table tag',
    },
    'core-graph', 2),
  record('src/core/theory.mli', 'Theory', 'namespace',
    'ns_ts ns_ls ns_pr ns_ns',
    'ns_ts ns_ls ns_pr ns_ns', {}, 'core-graph', 2),
  record('src/core/theory.mli', 'Theory', 'meta',
    'meta_name meta_type meta_excl meta_desc meta_tag',
    'meta_name meta_type meta_excl',
    {
      meta_desc: 'localized documentation text',
      meta_tag: 'runtime registration tag',
    },
    'core-graph', 2),
  record('src/core/theory.mli', 'Theory', 'theory',
    'th_name th_path th_decls th_ranges th_floats th_crcmap th_proved_wf ' +
    'th_export th_known th_local th_used',
    'th_name th_path th_decls th_export',
    {
      th_ranges: 'derived range projection index',
      th_floats: 'derived float projection index',
      th_crcmap: 'derived coercion closure reconstructed from declaration/meta history',
      th_proved_wf: 'derived well-foundedness index reconstructed from metas',
      th_known: 'derived known-declaration index',
      th_local: 'derived local-identifier set',
      th_used: 'derived used-theory set',
    },
    'core-graph', 2),
  record('src/core/theory.mli', 'Theory', 'tdecl',
    'td_node td_tag', 'td_node',
    { td_tag: 'runtime declaration tag' }, 'core-graph', 2),
  record('src/core/theory.mli', 'Theory', 'symbol_map',
    'sm_ty sm_ts sm_ls sm_pr',
    'sm_ty sm_ts sm_ls sm_pr', {}, 'core-graph', 2),
  record('src/core/task.mli', 'Task', 'tdecl_set',
    'tds_set tds_tag', '',
    {
      tds_set: 'derived task history set',
      tds_tag: 'runtime weak-table tag',
    },
    'task-graph', 2),
  record('src/core/task.mli', 'Task', 'task_hd',
    'task_decl task_prev task_known task_clone task_meta task_tag',
    'task_decl task_prev',
    {
      task_known: 'derived known-declaration index',
      task_clone: 'derived use/clone history',
      task_meta: 'derived meta history',
      task_tag: 'runtime weak-table tag',
    },
    'task-graph', 2),

  record('src/mlw/ity.mli', 'Ity', 'itysymbol',
    'its_ts its_nonfree its_private its_mutable its_fragile its_mfields ' +
    'its_ofields its_regions its_arg_flg its_reg_flg its_def',
    'its_ts its_nonfree its_private its_mutable its_fragile its_mfields ' +
    'its_ofields its_regions its_arg_flg its_reg_flg its_def',
    {}, 'mlw-type-graph', 3),
  record('src/mlw/ity.mli', 'Ity', 'its_flag',
    'its_frozen its_exposed its_liable its_fixed its_visible',
    'its_frozen its_exposed its_liable its_fixed its_visible',
    {}, 'mlw-type-graph', 3),
  record('src/mlw/ity.mli', 'Ity', 'ity',
    'ity_node ity_pure ity_tag', 'ity_node',
    {
      ity_pure: 'derived purity cache',
      ity_tag: 'runtime weak-table tag',
    },
    'mlw-type-graph', 3),
  record('src/mlw/ity.mli', 'Ity', 'region',
    'reg_name reg_its reg_args reg_regs',
    'reg_name reg_its reg_args reg_regs', {}, 'mlw-type-graph', 3),
  record('src/mlw/ity.mli', 'Ity', 'pvsymbol',
    'pv_vs pv_ity pv_ghost',
    'pv_vs pv_ity pv_ghost', {}, 'mlw-type-graph', 3),
  record('src/mlw/ity.mli', 'Ity', 'ity_subst',
    'isb_var isb_reg', 'isb_var isb_reg', {}, 'mlw-type-graph', 3),
  record('src/mlw/ity.mli', 'Ity', 'xsymbol',
    'xs_name xs_ity xs_mask',
    'xs_name xs_ity xs_mask', {}, 'mlw-type-graph', 3),
  record('src/mlw/ity.mli', 'Ity', 'effect',
    'eff_reads eff_writes eff_taints eff_covers eff_resets eff_raises ' +
    'eff_spoils eff_oneway eff_ghost',
    'eff_reads eff_writes eff_taints eff_covers eff_resets eff_raises ' +
    'eff_spoils eff_oneway eff_ghost',
    {}, 'mlw-type-graph', 3),
  record('src/mlw/ity.mli', 'Ity', 'cty',
    'cty_args cty_pre cty_post cty_xpost cty_oldies cty_effect cty_result ' +
    'cty_mask cty_freeze',
    'cty_args cty_pre cty_post cty_xpost cty_oldies cty_effect cty_result ' +
    'cty_mask cty_freeze',
    {}, 'mlw-type-graph', 3),

  record('src/mlw/expr.mli', 'Expr', 'rsymbol',
    'rs_name rs_cty rs_logic rs_field',
    'rs_name rs_cty rs_logic rs_field', {}, 'mlw-expression-graph', 3),
  record('src/mlw/expr.mli', 'Expr', 'prog_pattern',
    'pp_pat pp_ity pp_mask pp_fail',
    'pp_pat pp_ity pp_mask pp_fail', {}, 'mlw-expression-graph', 3),
  record('src/mlw/expr.mli', 'Expr', 'expr',
    'e_node e_ity e_mask e_effect e_attrs e_loc e_id',
    'e_node e_ity e_mask e_effect e_attrs e_loc',
    { e_id: 'runtime expression identifier' }, 'mlw-expression-graph', 3),
  record('src/mlw/expr.mli', 'Expr', 'cexp',
    'c_node c_cty', 'c_node c_cty', {}, 'mlw-expression-graph', 3),
  record('src/mlw/expr.mli', 'Expr', 'rec_defn',
    'rec_sym rec_rsym rec_fun rec_varl',
    'rec_sym rec_rsym rec_fun rec_varl', {}, 'mlw-expression-graph', 3),
  record('src/mlw/pdecl.mli', 'Pdecl', 'its_defn',
    'itd_its itd_fields itd_constructors itd_invariant itd_witness',
    'itd_its itd_fields itd_constructors itd_invariant itd_witness',
    {}, 'mlw-declaration-graph', 3),
  record('src/mlw/pdecl.mli', 'Pdecl', 'pdecl',
    'pd_node pd_pure pd_meta pd_syms pd_news pd_tag',
    'pd_node pd_pure pd_meta',
    {
      pd_syms: 'derived used-symbol set',
      pd_news: 'derived introduced-symbol set',
      pd_tag: 'runtime declaration tag',
    },
    'mlw-declaration-graph', 3),
  record('src/mlw/pmodule.mli', 'Pmodule', 'namespace',
    'ns_ts ns_ps ns_xs ns_ns',
    'ns_ts ns_ps ns_xs ns_ns', {}, 'mlw-module-graph', 4),
  record('src/mlw/pmodule.mli', 'Pmodule', 'pmodule',
    'mod_theory mod_units mod_export mod_known mod_local mod_used',
    'mod_theory mod_units mod_export',
    {
      mod_known: 'derived known-declaration index',
      mod_local: 'derived local-identifier set',
      mod_used: 'derived used-module set',
    },
    'mlw-module-graph', 4),
  record('src/mlw/pmodule.mli', 'Pmodule', 'mod_inst',
    'mi_mod mi_ty mi_ts mi_ls mi_pr mi_pk mi_pv mi_rs mi_xs mi_df',
    'mi_mod mi_ty mi_ts mi_ls mi_pr mi_pk mi_pv mi_rs mi_xs mi_df',
    {}, 'mlw-module-graph', 4),
];

const FULL_FILE_VARIANTS = [
  {
    id: 'PtreeFull.full_unit_kind.FullTheory',
    owner: 'PtreeFull',
    type: 'full_unit_kind',
    constructor: 'FullTheory',
    source: 'tools/why3_reference/patches/full-mlw-export.patch',
    layer: 'surface-file-envelope',
    migrationPhase: 1,
    targetLane: 'exact',
  },
  {
    id: 'PtreeFull.full_unit_kind.FullModule',
    owner: 'PtreeFull',
    type: 'full_unit_kind',
    constructor: 'FullModule',
    source: 'tools/why3_reference/patches/full-mlw-export.patch',
    layer: 'surface-file-envelope',
    migrationPhase: 1,
    targetLane: 'exact',
  },
  {
    id: 'PtreeFull.full_mlw_file.FullModules',
    owner: 'PtreeFull',
    type: 'full_mlw_file',
    constructor: 'FullModules',
    source: 'tools/why3_reference/patches/full-mlw-export.patch',
    layer: 'surface-file-envelope',
    migrationPhase: 1,
    targetLane: 'exact',
  },
  {
    id: 'PtreeFull.full_mlw_file.FullDecls',
    owner: 'PtreeFull',
    type: 'full_mlw_file',
    constructor: 'FullDecls',
    source: 'tools/why3_reference/patches/full-mlw-export.patch',
    layer: 'surface-file-envelope',
    migrationPhase: 1,
    targetLane: 'exact',
  },
];

const FULL_FILE_RECORDS = [
  {
    id: 'PtreeFull.full_unit',
    owner: 'PtreeFull',
    type: 'full_unit',
    source: 'tools/why3_reference/patches/full-mlw-export.patch',
    layer: 'surface-file-envelope',
    migrationPhase: 1,
    rawFields: ['full_kind', 'full_name', 'full_decls', 'full_loc'],
    canonicalV3Fields: ['full_kind', 'full_name', 'full_decls', 'full_loc'],
    excludedFromCanonicalV3: {},
  },
];

const OPAQUE_PROJECTIONS = [
  {
    id: 'Coercion.t',
    source: 'src/core/coercion.mli',
    canonicalV3Projection:
      'not serialized as an object; reconstructed from ordered theory declaration/meta history',
    layer: 'core-graph',
    migrationPhase: 2,
  },
  {
    id: 'Decl.ls_defn',
    source: 'src/core/decl.mli',
    canonicalV3Projection:
      'open_ls_defn yields ordered binders and body; decrease indexes are semantic',
    layer: 'core-graph',
    migrationPhase: 2,
  },
  {
    id: 'Dexpr.dity',
    source: 'src/mlw/dexpr.mli',
    canonicalV3Projection:
      'intermediate unification state is compared at the structured diagnostic boundary, not serialized in final typed graphs',
    layer: 'program-typing-ir',
    migrationPhase: 5,
  },
  {
    id: 'Dterm.dty',
    source: 'src/core/dterm.mli',
    canonicalV3Projection:
      'dty_fold projects symbols, variables, and unification variables without physical identity',
    layer: 'logic-typing-ir',
    migrationPhase: 2,
  },
  {
    id: 'Task.task',
    source: 'src/core/task.mli',
    canonicalV3Projection:
      'task_tdecls in semantic history order; task caches are excluded',
    layer: 'task-graph',
    migrationPhase: 2,
  },
  {
    id: 'Term.term_bound',
    source: 'src/core/term.mli',
    canonicalV3Projection:
      't_open_bound; binder encoded by type and de Bruijn position',
    layer: 'core-graph',
    migrationPhase: 2,
  },
  {
    id: 'Term.term_branch',
    source: 'src/core/term.mli',
    canonicalV3Projection:
      't_open_branch; pattern binders encoded by de Bruijn position',
    layer: 'core-graph',
    migrationPhase: 2,
  },
  {
    id: 'Term.term_quant',
    source: 'src/core/term.mli',
    canonicalV3Projection:
      't_open_quant; ordered binders, triggers, and body',
    layer: 'core-graph',
    migrationPhase: 2,
  },
].sort((left, right) => compareUtf8(left.id, right.id));

function verifyRoot(root) {
  const commit = runChecked('git', ['-C', root, 'rev-parse', 'HEAD']).trim();
  const tree = runChecked('git', ['-C', root, 'rev-parse', 'HEAD^{tree}']).trim();
  if (commit !== WHY3_COMMIT || tree !== WHY3_TREE) {
    fail(
      `Why3 source identity drift: expected ${WHY3_COMMIT}/${WHY3_TREE}, ` +
      `got ${commit}/${tree}`,
    );
  }
}

function withWhy3Root(options, action) {
  if (options.why3Archive === null) {
    verifyRoot(options.why3Root);
    return action(options.why3Root);
  }
  const archive = readFileSync(options.why3Archive);
  if (sha256(archive) !== WHY3_ARCHIVE_SHA256) {
    fail('Why3 archive hash drift');
  }
  const temporary = mkdtempSync(join(tmpdir(), 'why3-target-features-'));
  try {
    runChecked('tar', [
      '-xzf',
      options.why3Archive,
      '--strip-components=1',
      '-C',
      temporary,
    ]);
    return action(temporary);
  } finally {
    rmSync(temporary, { recursive: true, force: true });
  }
}

function buildContract(why3Root) {
  const sources = new Map();
  const masked = new Map();
  const sourcePaths = new Set([
    ...VARIANT_FAMILIES.map(family => family.source),
    ...RECORD_FAMILIES.map(family => family.source),
    ...OPAQUE_PROJECTIONS.map(entry => entry.source),
    'src/parser/parser.mly',
    'src/parser/typing.ml',
  ]);
  for (const path of [...sourcePaths].sort(compareUtf8)) {
    const bytes = readFileSync(join(why3Root, path));
    sources.set(path, {
      path,
      sha256: sha256(bytes),
      role: path === 'src/parser/parser.mly' ||
        path === 'src/parser/typing.ml'
        ? 'full-file grammar/interface semantics'
        : 'constructor and record-field inventory',
    });
    masked.set(path, maskOcamlComments(bytes.toString('utf8'), path));
  }

  const variants = [];
  for (const family of VARIANT_FAMILIES) {
    assertEqual(
      extractConstructors(masked.get(family.source), family.type, family.source),
      family.constructors,
      `${family.owner}.${family.type} constructors`,
    );
    for (const constructor of family.constructors) {
      variants.push({
        id: `${family.owner}.${family.type}.${constructor}`,
        owner: family.owner,
        type: family.type,
        constructor,
        source: family.source,
        layer: family.layer,
        migrationPhase: family.migrationPhase,
        targetLane: 'exact',
      });
    }
  }
  variants.push(...FULL_FILE_VARIANTS);
  variants.sort((left, right) => compareUtf8(left.id, right.id));
  if (new Set(variants.map(entry => entry.id)).size !== variants.length) {
    fail('duplicate target feature variant id');
  }

  const records = RECORD_FAMILIES.map(family => {
    assertEqual(
      extractRecordFields(masked.get(family.source), family.type, family.source),
      family.rawFields,
      `${family.owner}.${family.type} record fields`,
    );
    const classified = [
      ...family.canonicalFields,
      ...Object.keys(family.excluded),
    ];
    assertEqual(
      [...classified].sort(compareUtf8),
      [...family.rawFields].sort(compareUtf8),
      `${family.owner}.${family.type} canonical/excluded field partition`,
    );
    return {
      id: `${family.owner}.${family.type}`,
      owner: family.owner,
      type: family.type,
      source: family.source,
      layer: family.layer,
      migrationPhase: family.migrationPhase,
      rawFields: family.rawFields,
      canonicalV3Fields: family.canonicalFields,
      excludedFromCanonicalV3: family.excluded,
    };
  });
  records.push(...FULL_FILE_RECORDS);
  records.sort((left, right) => compareUtf8(left.id, right.id));

  const projectAstBytes = readFileSync(PROJECT_AST_INVENTORY_PATH);
  const projectAst = JSON.parse(projectAstBytes);
  if (projectAst.contract !== 'why3mbt-project-parser-ast-inventory-v1') {
    fail('unexpected project parser AST inventory contract');
  }
  const fullPatchBytes = readFileSync(FULL_MLW_PATCH_PATH);
  const sourceInventory = [...sources.values()];
  const sourceInventorySha256 = canonicalSha(sourceInventory);
  const variantInventorySha256 = canonicalSha(variants);
  const recordInventorySha256 = canonicalSha(records);
  const opaqueProjectionInventorySha256 = canonicalSha(OPAQUE_PROJECTIONS);

  return {
    schemaVersion: 2,
    contract: 'why3-1.7.2-complete-target-features-v2',
    why3Version: '1.7.2',
    why3Commit: WHY3_COMMIT,
    why3Tree: WHY3_TREE,
    policy: {
      targetLanes: ['exact', 'reject'],
      officialLegalBehavior: 'exact',
      officialIllegalShape: 'reject with structured stage/category/span',
      intentionalDivergenceCount: 0,
      englishDiagnosticMessageCompared: false,
      serializedIdentity:
        'first preorder encounter for symbols, regions, variables, exceptions, and routines',
      boundVariables: 'de Bruijn index',
      mapsAndSets: 'sorted by canonical key',
      excludedState: 'derived caches, runtime tags, physical identity, localized prose',
    },
    projectParserAstInventory: {
      path: 'tools/contracts/parser-ast-inventory-v1.json',
      sha256: sha256(projectAstBytes),
      enumCount: projectAst.counts.enums,
      variantCount: projectAst.counts.variants,
      note:
        'MoonBit parser/literal AST variants; not an upstream Ptree constructor inventory and not a support-lane contract',
    },
    fullFileGrammar: {
      categoryPreserved: ['theory', 'module'],
      moduleInterface: {
        representation: 'FullModule of qualid option',
        lane: 'exact',
        fixtures: [
          'bench/extraction/interface1/interface1.mlw',
          'examples/cursor_examples.mlw',
        ],
        parserEvidence: 'src/parser/parser.mly',
        semanticsEvidence: 'src/parser/typing.ml',
      },
      envelopePatch: {
        path: 'tools/why3_reference/patches/full-mlw-export.patch',
        sha256: sha256(fullPatchBytes),
      },
      parserCorpus: {
        total: 989,
        exact: 931,
        ptreeExact: 929,
        fullMainExact: 2,
        reject: 58,
        rejectMainEntry: 'why3 prove --parse-only',
        rejectStage: 'parsing',
        rejectCategory: 'Rejected',
      },
    },
    sourceInventory,
    sourceInventorySha256,
    counts: {
      variantFamilies: VARIANT_FAMILIES.length + 2,
      variants: variants.length,
      recordFamilies: records.length,
      opaqueProjections: OPAQUE_PROJECTIONS.length,
      canonicalV3Fields: records.reduce(
        (count, entry) => count + entry.canonicalV3Fields.length,
        0,
      ),
      excludedRawFields: records.reduce(
        (count, entry) =>
          count + Object.keys(entry.excludedFromCanonicalV3).length,
        0,
      ),
    },
    variants,
    variantInventorySha256,
    records,
    recordInventorySha256,
    opaqueProjections: OPAQUE_PROJECTIONS,
    opaqueProjectionInventorySha256,
  };
}

function render(options) {
  return withWhy3Root(
    options,
    root => `${JSON.stringify(buildContract(root), null, 2)}\n`,
  );
}

try {
  const options = parseArguments(process.argv.slice(2));
  const rendered = render(options);
  if (options.mode === 'output') {
    writeFileSync(options.path, rendered);
  } else if (options.mode === 'check') {
    if (readFileSync(options.path, 'utf8') !== rendered) {
      fail(`${options.path} does not match the generated target feature contract`);
    }
  } else {
    process.stdout.write(rendered);
  }
} catch (error) {
  process.stderr.write(`generate_target_feature_contract: ${error.message}\n`);
  process.exitCode = 1;
}
