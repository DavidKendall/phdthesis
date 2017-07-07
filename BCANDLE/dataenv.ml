type var = string
type omega = string
type gamma = string
type value = int
type valuation = (var * value) list
module ValuationSet = 
  Set.Make(struct type t = valuation let compare = compare end)
type valuation_set = ValuationSet.t
type operation = valuation -> valuation_set
type predicate = valuation_set
type operations = omega -> operation
type predicates = gamma -> predicate
type data_env = valuation * operations * predicates
