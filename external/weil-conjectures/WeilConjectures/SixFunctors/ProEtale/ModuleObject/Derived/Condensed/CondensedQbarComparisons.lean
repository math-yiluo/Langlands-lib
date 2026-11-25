/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-! # Specified condensed finite-to-Qbar comparison maps

The four comparison constructions are moved verbatim from the module
`CondensedQbarBaseChangeCompatibility` (in `WeilConjectures.SixFunctors.ProEtale.ModuleObject`),
so the exchange coherence lemma can use them
without an import cycle (blueprint: def-weil-pbc-qbar-condensed-comparisons).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

section Edge

variable {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
  [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]

/-- The canonical pullback comparison restricted to bounded constructible objects, in the
orientation `T_T l_{h,E} ≅ l_{h,Ω} T_U`. Source: ChangeOfCoefficients.lean, `derivedPullIso`;
TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarPullIso (K : PadicSubfieldConstructible U ℓ E) :
    (constructibleToPadicAlgCl T ℓ E).obj
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (h.asOver (Spec (.of k)))).obj K) ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (h.asOver (Spec (.of k)))).obj
        ((constructibleToPadicAlgCl U ℓ E).obj K) :=
  ObjectProperty.isoMk _
    ((derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h).app K.obj)

/-- The specified pushforward comparison restricted to bounded constructible objects.
Source: ChangeOfCoefficients.lean, `derivedPushHom`, the mate of restriction/pushforward;
TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarPushHom (K : PadicSubfieldConstructible T ℓ E) :
    (constructibleToPadicAlgCl U ℓ E).obj
        ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
            (h.asOver (Spec (.of k)))).obj K) ⟶
      (boundedConstructibleLowerStar ℓ
          (h.asOver (Spec (.of k)))).obj
        ((constructibleToPadicAlgCl T ℓ E).obj K) :=
  ObjectProperty.homMk
    ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h).app K.obj)

end Edge

section Square

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- The specified source comparison `S_K`: first the pull comparison for `g`, then the
pullback of the push comparison for `f`. Source: TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarSourceHom (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgCl Y' ℓ E).obj
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (g.asOver (Spec (.of k)))).obj
          ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
              (f.asOver (Spec (.of k)))).obj K)) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (g.asOver (Spec (.of k)))).obj
        ((boundedConstructibleLowerStar ℓ
            (f.asOver (Spec (.of k)))).obj
          ((constructibleToPadicAlgCl X ℓ E).obj K)) :=
  (constructibleToQbarPullIso ℓ k E g
      ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
          (f.asOver (Spec (.of k)))).obj K)).hom ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (g.asOver (Spec (.of k)))).map
      (constructibleToQbarPushHom ℓ k E f K)

/-- The specified target comparison `U_K`: first the push comparison for `f'`, then the
pushforward of the pull comparison for `g'`. Source: TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarTargetHom (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgCl Y' ℓ E).obj
        ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
            (f'.asOver (Spec (.of k)))).obj
          ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
              (g'.asOver (Spec (.of k)))).obj K)) ⟶
      (boundedConstructibleLowerStar ℓ
          (f'.asOver (Spec (.of k)))).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (g'.asOver (Spec (.of k)))).obj
          ((constructibleToPadicAlgCl X ℓ E).obj K)) :=
  constructibleToQbarPushHom ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (g'.asOver (Spec (.of k)))).obj K) ≫
    (boundedConstructibleLowerStar ℓ (f'.asOver (Spec (.of k)))).map
      (constructibleToQbarPullIso ℓ k E g' K).hom

end Square

end AlgebraicGeometry.ProEtale.CondensedRing
