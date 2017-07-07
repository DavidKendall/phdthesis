typedef struct {
  uchar _VAR__  : 1;
  uchar _VAR_p  : 1;
  uchar _VAR_w1 : 2;
  uchar _VAR_w2 : 2;
} data_env_t;

static data_env_t temp;
 
void
OP_ReadWaterLevel(data_env_t *env, stack_t *data) {
  temp = *env;
  temp._VAR_w1 = 0; 
  push(data,&temp);
  temp._VAR_w1 = 1; 
  push(data,&temp);
  temp._VAR_w1 = 2; 
  push(data,&temp);
}

void
OP_ID(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_InitSensor(data_env_t *env, stack_t *data) {
  temp = *env;
  temp._VAR_w1 = 1; 
  push(data,&temp);
}

void
OP_InitPump(data_env_t *env, stack_t *data) {
  temp = *env;
  temp._VAR_p = 0; 
  push(data,&temp);
}

void
OP_InitController(data_env_t *env, stack_t *data) {
  temp = *env;
  temp._VAR_w2 = 1; 
  push(data,&temp);
}

void
OP_C_ReadyDelay(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_WL_ReadyPeriod(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_WL_NormalPeriod(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_P_ReadyPeriod(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_P_NormalPeriod(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_SensorFailed(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_PumpOn(data_env_t *env, stack_t *data) {
  temp = *env;
  temp._VAR_p = 1; 
  push(data,&temp);
}

void
OP_PumpOff(data_env_t *env, stack_t *data) {
  temp = *env;
  temp._VAR_p = 0; 
  push(data,&temp);
}

void
OP_TestHighLevel(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_TestLowLevel(data_env_t *env, stack_t *data) {
  push(data,env);
}

void
OP_SensorTimedOut(data_env_t *env, stack_t *data) {
  push(data,env);
}

int
PRED_LowLevel(data_env_t *env) {
  return (env->_VAR_w2 == 0);
}

int
PRED_notLowLevel(data_env_t *env) {
  return !PRED_LowLevel(env);
}

int
PRED_HighLevel(data_env_t *env) {
  return (env->_VAR_w2 == 2);
}

int
PRED_notHighLevel(data_env_t *env) {
  return !PRED_HighLevel(env);
}

int
PRED___true(data_env_t *env) {
  return (1);
}

int
PRED___false(data_env_t *env) {
  return (0);
}





