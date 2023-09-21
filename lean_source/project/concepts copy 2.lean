-- Stubbed out basic types
inductive concept | mk
inductive event | mk
inductive action | mk
inductive bool_expr | mk
inductive app_state | mk
inductive bool_var | mk
 
def bool_env_type : Type := bool_var → bool
 
variables
 (bool_env : bool_var → bool)
 (bool_expr_eval : bool_expr → bool_env_type → bool)
 
inductive app 
| skip
| atomic (c : concept) : app
| free (a1 a2 : app) : app
| seq (a1 a2 : app) : app
| if_then_else (c : bool_expr) (t : app) (f : app) : app
| while (c : bool_expr) (b : app) : app
| secure (auth : app) (a: app)
open app
 
def app_eval : app → app_state → unit
| a st := unit.star
 
-- account for runtime event/action wiring and setup for that separately
 
variables 
 (thermometer survey resources auth: app)
 (condition : bool_expr)
 
/-
Here's a model of our app. Dooes it capture it (but for the outer loop)?
-/
-- instructions in imperative programs have well defined impacts on state. so too must our concepts.
def md : app := 
 seq 
   (while (condition) auth) -- condition will be based on something auth or previous concept does to the state.
   (seq 
     (thermometer) -- thermometer and 
     (seq -- sequential composition of   -- doesnt capture data passing bc assumed shared state. shared state is realized by api calls?
       (survey) -- survey and 
       (if_then_else -- conditionally run resources
         (condition)
         (resources)
         (skip) -- or do nothing
       )
     )
   ) -- body end, loop back

variables 
  (library reader lock messenger: app)
  (is_driving: bool_expr)

def seq_example: app := 
  seq library reader

def loop_example: app := 
  while (is_driving) lock

def inductive_example: app := 
  seq (while (is_driving) lock) messenger


  def eval : app → (concept → string) → string
  | (atomic c) i := i c
  | (seq a b) i := s!"{}"
  | _ _ := ""