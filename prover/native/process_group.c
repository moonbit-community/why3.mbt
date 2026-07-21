// SPDX-License-Identifier: LGPL-2.1-only WITH OCaml-LGPL-linking-exception

#include <moonbit.h>

#ifdef _WIN32

#include <process.h>
#include <stdlib.h>

MOONBIT_FFI_EXPORT
void why3mbt_launch_process_group_from_environment(void) {
  _exit(126);
}

MOONBIT_FFI_EXPORT
void why3mbt_kill_process_group(int32_t pid) {
  (void)pid;
}

#else

#include <errno.h>
#include <signal.h>
#include <spawn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef __linux__
#include <sys/prctl.h>
#endif
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

extern char **environ;

static const char *const internal_prefix = "WHY3MBT_INTERNAL_";
static volatile sig_atomic_t cancellation_requested = 0;
static volatile sig_atomic_t active_child = -1;

static void request_cancellation(int signal_number) {
  int saved_errno = errno;
  (void)signal_number;
  cancellation_requested = 1;
  pid_t child = (pid_t)active_child;
  if (child > 1) {
    kill(-child, SIGKILL);
  }
  errno = saved_errno;
}

static int is_internal_environment_entry(const char *entry) {
  return strncmp(entry, internal_prefix, strlen(internal_prefix)) == 0;
}

static char **filtered_environment(void) {
  size_t count = 0;
  for (char **entry = environ; *entry != NULL; ++entry) {
    if (!is_internal_environment_entry(*entry)) {
      ++count;
    }
  }
  char **result = calloc(count + 1, sizeof(char *));
  if (result == NULL) {
    return NULL;
  }
  size_t index = 0;
  for (char **entry = environ; *entry != NULL; ++entry) {
    if (!is_internal_environment_entry(*entry)) {
      result[index++] = *entry;
    }
  }
  return result;
}

static void launcher_failure(const char *operation, int error_code, int status) {
  dprintf(STDERR_FILENO, "why3mbt process-group launcher: %s: %s\n",
          operation, strerror(error_code));
  _exit(status);
}

static void install_cancellation_handler(void) {
  struct sigaction action;
  memset(&action, 0, sizeof(action));
  action.sa_handler = request_cancellation;
  sigemptyset(&action.sa_mask);
  if (sigaction(SIGTERM, &action, NULL) < 0) {
    launcher_failure("sigaction", errno, 126);
  }
}

static void become_subreaper(void) {
#ifdef __linux__
  if (prctl(PR_SET_CHILD_SUBREAPER, 1) < 0) {
    launcher_failure("prctl(PR_SET_CHILD_SUBREAPER)", errno, 126);
  }
#endif
}

MOONBIT_FFI_EXPORT
void why3mbt_launch_process_group_from_environment(void) {
  const char *executable = getenv("WHY3MBT_INTERNAL_EXECUTABLE");
  const char *argc_text = getenv("WHY3MBT_INTERNAL_ARGC");
  if (executable == NULL || executable[0] == '\0' || argc_text == NULL) {
    launcher_failure("invalid launcher environment", EINVAL, 126);
  }
  char *end = NULL;
  long argument_count = strtol(argc_text, &end, 10);
  if (end == argc_text || *end != '\0' || argument_count < 0 ||
      argument_count > 1024) {
    launcher_failure("invalid argument count", EINVAL, 126);
  }
  char **arguments = calloc((size_t)argument_count + 2, sizeof(char *));
  if (arguments == NULL) {
    launcher_failure("allocate argv", ENOMEM, 126);
  }
  arguments[0] = (char *)executable;
  for (long index = 0; index < argument_count; ++index) {
    char key[64];
    snprintf(key, sizeof(key), "WHY3MBT_INTERNAL_ARG_%ld", index);
    arguments[index + 1] = getenv(key);
    if (arguments[index + 1] == NULL) {
      launcher_failure("missing argument", EINVAL, 126);
    }
  }

  char **child_environment = filtered_environment();
  if (child_environment == NULL) {
    launcher_failure("allocate environment", ENOMEM, 126);
  }
  if (setsid() < 0) {
    launcher_failure("setsid", errno, 126);
  }
  install_cancellation_handler();
  become_subreaper();

  pid_t child = -1;
  posix_spawnattr_t spawn_attributes;
  int spawn_error = posix_spawnattr_init(&spawn_attributes);
  if (spawn_error != 0) {
    launcher_failure("posix_spawnattr_init", spawn_error, 126);
  }
  spawn_error = posix_spawnattr_setflags(
    &spawn_attributes,
    POSIX_SPAWN_SETPGROUP
  );
  if (spawn_error != 0) {
    launcher_failure("posix_spawnattr_setflags", spawn_error, 126);
  }
  spawn_error = posix_spawnattr_setpgroup(&spawn_attributes, 0);
  if (spawn_error != 0) {
    launcher_failure("posix_spawnattr_setpgroup", spawn_error, 126);
  }
  spawn_error = posix_spawnp(
    &child,
    executable,
    NULL,
    &spawn_attributes,
    arguments,
    child_environment
  );
  posix_spawnattr_destroy(&spawn_attributes);
  if (spawn_error != 0) {
    launcher_failure(
      "posix_spawnp",
      spawn_error,
      spawn_error == ENOENT ? 127 : 126
    );
  }
  active_child = (sig_atomic_t)child;
  if (cancellation_requested) {
    kill(-child, SIGKILL);
  }

  int child_status = 0;
  int child_reaped = 0;
  for (;;) {
    int wait_status = 0;
    pid_t reaped = waitpid(-1, &wait_status, 0);
    if (reaped > 0) {
      if (reaped == child) {
        child_status = wait_status;
        child_reaped = 1;
        // The solver root owns the whole target process group. Do not let a
        // detached helper keep pipes open or survive after that root exits.
        kill(-child, SIGKILL);
      }
      if (cancellation_requested) {
        kill(-child, SIGKILL);
      }
      continue;
    }
    if (errno == EINTR) {
      if (cancellation_requested) {
        kill(-child, SIGKILL);
      }
      continue;
    }
    if (errno == ECHILD) {
      break;
    }
    launcher_failure("waitpid", errno, 126);
  }
  active_child = -1;
  if (cancellation_requested) {
    _exit(130);
  }
  if (!child_reaped) {
    launcher_failure("waitpid lost target", ECHILD, 126);
  }
  if (WIFEXITED(child_status)) {
    _exit(WEXITSTATUS(child_status));
  }
  if (WIFSIGNALED(child_status)) {
    _exit(128 + WTERMSIG(child_status));
  }
  _exit(126);
}

MOONBIT_FFI_EXPORT
void why3mbt_kill_process_group(int32_t pid) {
  if (pid <= 1) {
    return;
  }
  kill((pid_t)pid, SIGTERM);
}

#endif
