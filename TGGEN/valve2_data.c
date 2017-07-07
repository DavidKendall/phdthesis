typedef struct {
  uchar _VAR_x;
  uchar _VAR_y1;
  uchar _VAR_z1;
  uchar _VAR_y2;
  uchar _VAR_z2;
} data_env_t;

void
OP_ID(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_ReadSensor(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_AdjustValve1(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_AdjustValve2(data_env_t *env, stack_t *data) {
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
