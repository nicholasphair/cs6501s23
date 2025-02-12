/-
USER POOL workflow
-/

-- used in sign-in process
inductive user : Type
def users := list user

-- returned by login-process (e.g., signed JSON web token (JWT))
inductive id_token

-- we haven't been dealing with these
inductive claim
def claims := list claim

structure time : Type := 
(n : ℕ) -- e.g, in seconds since epoch start


structure access_token : Type := 
(cl : claims)
(exp : time)

#check @access_token

structure refresh_token :=
(exp : time)

inductive less_or_eq (t1 t2 : time) : Prop

structure authnz_tokens :=
(id : id_token)
(acc : access_token)
(ref : refresh_token)
(rel_exp : less_or_eq ref.exp acc.exp)   -- e.g., access token 2 minutes, refresh token 2 days
                                         -- access token expires, present ref. token to get a new one

#check authnz_tokens 
/-
Note: Amplify library takes care of a lot of the details of refreshing access tokens. 
-/

inductive username : Type    -- relation to user and to account?   
inductive password : Type

/-
In our application, approx the Cognito sign-up procedure.
This procedure clearly combines aspects of authentication of 
identity and corresponding authorizations in the form of the 
access token returned within the authnz_tokens structure. 
-/
def cognito_login : username → password → option authnz_tokens := sorry

-- more limited case of returned tokens vs authnz_tokens
structure access_ref_tokens :=
(acc : access_token)
(ref : refresh_token)


-- separate the authn and authz concerns in the design 
def better_login : username → password → option id_token := sorry     -- contains a timeout in some way
def get_authorizations : id_token → option access_ref_tokens := sorry 
-- get_authorizations can fail, e.g., if you present an untrusted or timed-out id_token 

/-
Cognito does support get_authorizations given an id_token but not (?) stand-alone authn.
When you rely on someone else to do authn we're talking federated identities or fed signin.
Third party is "identity provider."
-/

-- Stubbed out basic types
inductive concept   | mk
inductive event     | mk
inductive action    | mk
inductive bool_expr | mk
inductive app_state | mk
inductive bool_var  | mk

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
def md : app := 
  seq 
    (while (condition) auth)
    (seq 
      (thermometer)    -- thermometer and  
      (seq             -- sequential composition of 
        (survey)      -- survey and
        (if_then_else -- conditionally run resources
          (condition)
          (resources)
          (skip)      -- or do nothing
        )
      )
    )                 -- body end, loop back
  
