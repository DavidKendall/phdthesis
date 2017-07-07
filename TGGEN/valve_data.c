typedef struct {
  uchar _VAR__;
} data_env_t;

void
OP_PERIOD(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_ReadSensor(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_AdjustValve(data_env_t *env, stack_t *data) {
  push(data,env);
}

int
PRED___true(data_env_t *env) {
  return (1);
}

int
PRED___false(data_env_t *env) {
  return (0);
}
