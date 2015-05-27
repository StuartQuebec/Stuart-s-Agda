{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
  ScopedTypeVariables, NoMonomorphismRestriction #-}
module MAlonzo.Code.BasicTypes where
import qualified MAlonzo.RTE
name1 = "BasicTypes.Level"
d1
  = error
      "MAlonzo Runtime Error: postulate evaluated: BasicTypes.Level"
name2 = "BasicTypes.lzero"
name3 = "BasicTypes.lsuc"
name4 = "BasicTypes._\8852_"
name5 = "BasicTypes.\8469"
d5 = ()
 
data T5 a0 = C6
           | C7 a0
name6 = "BasicTypes.\8469.zero"
name7 = "BasicTypes.\8469.suc"
name9 = "BasicTypes.Type"
d9 v0 = MAlonzo.RTE.mazCoerce ()
name11 = "BasicTypes.Type\8320"
d11 = MAlonzo.RTE.mazCoerce ()
name12 = "BasicTypes.Type\8321"
d12 = MAlonzo.RTE.mazCoerce ()
name13 = "BasicTypes.Typ"
d13 = MAlonzo.RTE.mazCoerce d11
name16 = "BasicTypes.Maybe"
d16 a0 a1 = ()
 
data T16 a0 = C20 a0
            | C21
name20 = "BasicTypes.Maybe.just"
name21 = "BasicTypes.Maybe.nothing"
name22 = "BasicTypes.\8869"
d22 = ()
 
data T22
name23 = "BasicTypes.Bool"
d23 = ()
 
data T23 = C24
         | C25
name24 = "BasicTypes.Bool.true"
name25 = "BasicTypes.Bool.false"
name28 = "BasicTypes.\172"
d28 v0 v1 = MAlonzo.RTE.mazCoerce ()
name38 = "BasicTypes._\176_"
d38 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazCoerce
      (\ v8 ->
         v6 (MAlonzo.RTE.mazCoerce (v7 (MAlonzo.RTE.mazCoerce v8))))
name46 = "BasicTypes.const"
d46 v0 v1 v2 v3 v4 = MAlonzo.RTE.mazCoerce (\ v5 -> v4)
name51 = "BasicTypes.id"
d51 v0 v1 = MAlonzo.RTE.mazCoerce (\ v2 -> v2)
name63 = "BasicTypes.flipDouble"
d63 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = MAlonzo.RTE.mazCoerce
      (v8 (MAlonzo.RTE.mazCoerce v11) (MAlonzo.RTE.mazCoerce v9)
         (MAlonzo.RTE.mazCoerce v10))
name76 = "BasicTypes.asdf"
d76 v0 v1 v2 v3 v4 v5
  = MAlonzo.RTE.mazCoerce
      (d63
         (MAlonzo.RTE.mazCoerce
            (d4 (MAlonzo.RTE.mazCoerce v2) (MAlonzo.RTE.mazCoerce v1)))
         (MAlonzo.RTE.mazCoerce
            (d4 (MAlonzo.RTE.mazCoerce v1) (MAlonzo.RTE.mazCoerce v0)))
         (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce ())
         (MAlonzo.RTE.mazCoerce ())
         (MAlonzo.RTE.mazCoerce v3)
         (MAlonzo.RTE.mazCoerce v5)
         (MAlonzo.RTE.mazCoerce
            (d38 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
               (MAlonzo.RTE.mazCoerce v2)
               (MAlonzo.RTE.mazCoerce v3)
               (MAlonzo.RTE.mazCoerce v4)
               (MAlonzo.RTE.mazCoerce v5))))
name81 = "BasicTypes.\8721"
d81 a0 a1 a2 a3 = ()
 
data T81 a0 a1 = C87 a0 a1
name87 = "BasicTypes.\8721._,_"
name92 = "BasicTypes.proj\8321"
d92 v0 v1 v2 v3 (C87 v4 v5) = MAlonzo.RTE.mazCoerce v4
d92 v0 v1 v2 v3 v4 = MAlonzo.RTE.mazIncompleteMatch name92
name100 = "BasicTypes.proj\8322"
d100 v0 v1 v2 v3 (C87 v4 v5) = MAlonzo.RTE.mazCoerce v5
d100 v0 v1 v2 v3 v4 = MAlonzo.RTE.mazIncompleteMatch name100
name107 = "BasicTypes._\215_"
d107 v0 v1 v2 v3
  = MAlonzo.RTE.mazCoerce
      (d81 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce v2)
         (MAlonzo.RTE.mazCoerce (\ v4 -> v3)))
name118 = "BasicTypes.rec\215"
d118 v0 v1 v2 v3 v4 v5 v6 (C87 v7 v8)
  = MAlonzo.RTE.mazCoerce
      (v6 (MAlonzo.RTE.mazCoerce v7) (MAlonzo.RTE.mazCoerce v8))
d118 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazIncompleteMatch name118
name131 = "BasicTypes.ind\215"
d131 v0 v1 v2 v3 v4 v5 (C87 v6 v7)
  = MAlonzo.RTE.mazCoerce
      (v5 (MAlonzo.RTE.mazCoerce v6) (MAlonzo.RTE.mazCoerce v7))
d131 v0 v1 v2 v3 v4 v5 v6 = MAlonzo.RTE.mazIncompleteMatch name131
name147 = "BasicTypes.2ind\215"
d147 v0 v1 v2 v3 v4 v5 (C87 v6 v7) (C87 v8 v9)
  = MAlonzo.RTE.mazCoerce
      (v5 (MAlonzo.RTE.mazCoerce v6) (MAlonzo.RTE.mazCoerce v7)
         (MAlonzo.RTE.mazCoerce v8)
         (MAlonzo.RTE.mazCoerce v9))
d147 v0 v1 v2 v3 v4 v5 v6 v7
  = MAlonzo.RTE.mazIncompleteMatch name147
name155 = "BasicTypes.const\8469"
d155 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d46 (MAlonzo.RTE.mazCoerce v0)
         (MAlonzo.RTE.mazCoerce (d3 (MAlonzo.RTE.mazCoerce d2)))
         (MAlonzo.RTE.mazCoerce v1)
         (MAlonzo.RTE.mazCoerce ())
         (MAlonzo.RTE.mazCoerce d5))
name156 = "BasicTypes.pred"
d156 (C6) = MAlonzo.RTE.mazCoerce C21
d156 v0
  = MAlonzo.RTE.mazCoerce (d_1_156 (MAlonzo.RTE.mazCoerce v0))
  where d_1_156 (C7 v0)
          = MAlonzo.RTE.mazCoerce (C20 (MAlonzo.RTE.mazCoerce v0))
        d_1_156 v0 = MAlonzo.RTE.mazIncompleteMatch name156
name158 = "BasicTypes._+_"
d158 (C6) v0 = MAlonzo.RTE.mazCoerce v0
d158 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d_1_158 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
  where d_1_158 (C7 v0) v1
          = MAlonzo.RTE.mazCoerce
              (C7
                 (MAlonzo.RTE.mazCoerce
                    (d158 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
        d_1_158 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name158
name162 = "BasicTypes._*_"
d162 (C6) v0 = MAlonzo.RTE.mazCoerce C6
d162 v0 v1
  = MAlonzo.RTE.mazCoerce
      (d_1_162 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))
  where d_1_162 (C7 v0) v1
          = MAlonzo.RTE.mazCoerce
              (d158 (MAlonzo.RTE.mazCoerce v0)
                 (MAlonzo.RTE.mazCoerce
                    (d162 (MAlonzo.RTE.mazCoerce v0) (MAlonzo.RTE.mazCoerce v1))))
        d_1_162 v0 v1 = MAlonzo.RTE.mazIncompleteMatch name162
 
{-# RULES
"mazNatToInteger-mazIntegerToNat" forall x .
                                  mazNatToInteger (mazIntegerToNat x) = x
"mazIntegerToNat-mazNatToInteger" forall x .
                                  mazIntegerToNat (mazNatToInteger x) = x
 #-}
mazNatToInteger
  = \ x -> case x of { C6 -> 0 :: Integer; C7 x -> 1 + (mazNatToInteger (MAlonzo.RTE.mazCoerce x)) }
mazIntegerToNat
  = \ x -> if x <= (0 :: Integer) then C6 else C7 (MAlonzo.RTE.mazCoerce (mazIntegerToNat (x - 1)))
 
{-# RULES
"mazNatToInt-mazIntToNat" forall x . mazNatToInt (mazIntToNat x) =
                          x
"mazIntToNat-mazNatToInt" forall x . mazIntToNat (mazNatToInt x) =
                          x
 #-}
mazNatToInt
  = \ x -> case x of { C6 -> 0 :: Int; C7 x -> 1 + (mazNatToInt (MAlonzo.RTE.mazCoerce x)) }
mazIntToNat
  = \ x -> if x <= (0 :: Int) then C6 else C7 (MAlonzo.RTE.mazCoerce (mazIntToNat (x - 1)))