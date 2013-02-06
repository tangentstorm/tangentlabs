
module Expr.Quote (ex) where

import Data.Generics
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote

import Expr

ex :: QuasiQuoter
ex = QuasiQuoter quoteExprExp quoteExprPat



quoteExprExp :: String -> TH.ExpQ
---------------------------------
quoteExprExp s = do loc <- TH.location
                    let pos = (TH.loc_filename loc,
                               fst (TH.loc_start loc),
                               snd (TH.loc_start loc))
                    expr <- parseExpr pos s
                    dataToExpQ (const Nothing `extQ` antiExprExp) expr




quoteExprPat :: String -> TH.PatQ
---------------------------------
quoteExprPat s = do loc <- TH.location
                    let pos = (TH.loc_filename loc,
                              fst (TH.loc_start loc),
                              snd (TH.loc_start loc))
                    expr <- parseExpr pos s
                    dataToPatQ (const Nothing `extQ` antiExprPat) expr


antiExprExp :: Expr -> Maybe (TH.Q TH.Exp)
------------------------------------------
antiExprExp (AntiIntExpr v) = Just $ TH.appE (TH.conE (TH.mkName "IntExpr"))
                                             (TH.varE (TH.mkName v))
antiExprExp (AntiExpr v)    = Just $ TH.varE (TH.mkName v)
antiExprExp _               = Nothing





antiExprPat :: Expr -> Maybe (TH.Q TH.Pat)
------------------------------------------
antiExprPat  (AntiIntExpr v)  = Just $ TH.conP  (TH.mkName "IntExpr")
                                                [TH.varP (TH.mkName v)]
antiExprPat  (AntiExpr v)     = Just $ TH.varP  (TH.mkName v)
antiExprPat  _                = Nothing




