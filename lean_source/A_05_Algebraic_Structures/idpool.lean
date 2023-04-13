/-
ID POOL workflow
-/

import .nick

inductive authn_provider: Type
| cognito: string → string → authn_provider -- userpool_id → app_client_id → authn_provider
| amazon: string → authn_provider  -- app_id → authn_provider
| apple: string → authn_provider -- app_id → authn_provider
| openId: authn_provider
| saml: authn_provider

-- need to capture the signin function a provider offers.
structure authn_provider_structure: Type :=
(provider: authn_provider)
(signin: string → string → id_token)

inductive iam_policy : Type
| from_json : string → iam_policy

inductive iam_role : Type
| mk : iam_policy → iam_policy → iam_role


structure idpool : Type :=
(provider : authn_provider_structure)
(default_auth_rule: iam_role)
(default_unauth_rule: iam_role)
(role_selector : claims → iam_role)

-- authn_provider offers a signin mechanism that returns a ID token.
-- id_token is then used to determine a role.