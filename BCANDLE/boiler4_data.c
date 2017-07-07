typedef struct {
  uchar _VAR__  : 1;
  uchar _VAR_v1 : 1;
  uchar _VAR_v2 : 1;
} data_env_t;

static data_env_t temp;
 
void
OP_ReadTemperature(data_env_t *env, stack_t *data) {
  temp = *env;
  temp._VAR_v1 = 0; 
  push(data,&temp);
  temp._VAR_v1 = 1; 
  push(data,&temp);
}

void
OP_ID(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_SensorFailed(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_TemperaturePostRcv(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_ControlPostRcv(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_Period(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_Configure(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_Timeout(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_SensorFailureDetected(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_ContinueAfterTempOk(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_ControlPostRcvAndEvalGuard(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_skip(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_RecoverControl(data_env_t *env, stack_t *data) {
  push(data,env);
}

int
PRED_TempOk(data_env_t *env) {
  return (env->_VAR_v2 == 0);
}

int
PRED_TempNok(data_env_t *env) {
  return (!(PRED_TempOk(env)));
}

int
PRED___true(data_env_t *env) {
  return (1);
}

int
PRED___false(data_env_t *env) {
  return (0);
}



