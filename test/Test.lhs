> module Main where

> import           System.Environment
> import           Test.DocTest
> import           Test.QuickCheck.Property
> import           Test.Tasty
> import           Test.Tasty.Ingredients.Basic
> import           Test.Tasty.QuickCheck
> import           Test.Tasty.Runners

> import Fungus



> main :: IO ()
> main = do
>   all_doctests
>   -- setEnv "TASTY_HIDE_SUCCESSES" "TRUE"
>   defaultMain $
>     localOption (NumThreads 6) $
>     localOption (QuickCheckTests 10000) $
>     test_Fungus

> all_doctests :: IO ()
> all_doctests = doctest
>   [ "-XLambdaCase"
>   , "-XInstanceSigs"
>   , "-XBangPatterns"
>   , "-XTypeApplications"
>   , "-XOverloadedStrings"
>   , "-XScopedTypeVariables"
>   , "-XAllowAmbiguousTypes"
> 
>   , "-package fungus"
> 
>   , "src/Fungus/LambdaTerm.lhs"
>   ]

> test_Fungus :: TestTree
> test_Fungus = testGroup "Fungus"
>   [ let title = "LambdaTerm" in
>     testGroup title
>     [ testProperty "height <= size" $
>         prop_heightOfLambdaTerm_lt_sizeOfLambdaTerm @(LambdaTerm ())
> 
>     , testProperty "fv(sigma[z]) = U_{t in fv(z)} fv(sigma(t))" $
>         prop_free_vars_in_applied_lambda_sub @(LambdaTerm ())
> 
>     , testProperty "fv(sigma_{y/x}[z]) = U_{t in fv(z)\\x} fv(sigma(t)) u {y}?" $
>         prop_free_vars_in_applied_pointwise_update_sub @(())
> 
>     , testProperty "(sigma1 sigma2)[z] == sigma1[sigma2[z]]" $
>         prop_lambda_sub_action @(())
> 
>     , testProperty "sigma id == sigma" $
>         prop_lambda_sub_composite_right_identity @(())
> 
>     , testProperty "id sigma ==α sigma" $
>         prop_lambda_sub_composite_left_identity @(())
> 
>     , testProperty "sigma3 (sigma2 sigma1) == (sigma3 sigma2) sigma1" $
>         prop_lambda_sub_composite_associative @(())
> 
>     , testProperty "alpha equivalence is reflexive" $
>         prop_alpha_eq_reflexive @(())
> 
>     , testProperty "alpha equivalence is symmetric" $
>         prop_alpha_eq_symmetric @(())
> 
>     , testProperty "alpha equivalence is transitive" $
>         prop_alpha_eq_transitive @(())
> 
>     , testProperty "if y notin fv(e) then λx.z ==α λy.id{y/x}[e]" $
>         prop_lambda_expr_alpha_eq_lemma @(())
> 
>     , testProperty "if y notin fv(e2) then @let x=e1 @in e2 ==α @let y=e1 @in id{y/x}[e2]" $
>         prop_let_expr_alpha_eq_lemma @(())
> 
>     , testProperty "if z ==α w then fv(z) == fv(w)" $
>         prop_alpha_eq_implies_same_free_vars @(())
> 
>     , testProperty "id[z] ==α z" $
>         prop_identity_subst_alpha_eq @(())
>     ]
>   ]
