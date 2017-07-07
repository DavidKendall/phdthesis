typedef struct {
  uchar _VAR__  : 1;
  uchar _VAR_v1 : 1;
  uchar _VAR_v2 : 1;
} data_env_t;
 
void
OP_ReadTemperature(data_env_t *env, stack_t *data) {
  data_env_t temp = *env;
  temp._VAR_v1 = 0; 
  push(data,&temp);
  temp = *env;
  temp._VAR_v1 = 1; 
  push(data,&temp);
}

void
OP_ID(data_env_t *env, stack_t *data) {
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
OP_RecoverSensorFailure(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_skip(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_RecoverTemperatureControl(data_env_t *env, stack_t *data) {
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




