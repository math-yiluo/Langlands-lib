/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStarDeligne
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicFiniteness

/-!

# The derived pushforward along a proper morphism on bounded constructible complexes

The proper direct image of constructible complexes: for a proper morphism
`p : X ⟶ Y` of `k`-schemes of finite type, `ℓ` invertible in `k`, the derived pushforward `Rp_*`
carries bounded constructible complexes to bounded constructible complexes, for each of the three
`ℓ`-adic coefficient rings `ℚ̲̄_ℓ`, `E̲` and `𝒪̲_E`. The proof is
`boundedConstructible_rightDerivedLowerStar_of_isProper_*_of_finiteType`
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdicFiniteness`):
integral models, inverting `ℓ` and the continuity of cohomology. It does not go through Deligne's
finiteness theorem for arbitrary `f` (`boundedConstructible_rightDerivedLowerStar_obj`).

This file bundles that proper-only finiteness into the functor and the adjunction that the
constructions of `Rf_! = i_! ⋙ Rp_*`, its independence of the compactification, composition and
base change, and `f^!` use for the proper leg, in the setting of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` (morphisms of
`Over (Spec (.of k))`), for each coefficient ring:

* `boundedConstructible_rightDerivedLowerStar_obj_of_isProper`: `Rp_*` preserves bounded
  constructible complexes for `p` proper;
* `boundedConstructibleLowerStarOfIsProper`, `boundedConstructibleLowerStarOfIsProperCompatibility`:
  the restriction of `R((p)_*⟦Λ⟧)` to `Dᵇc(-)⟦Λ⟧`;
* the adjunction `Lp^* ⊣ Rp_*` (`boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper`) and
  the composition isomorphism `boundedConstructibleLowerStarOfIsProperComp`;
* `boundedConstructibleLowerStarOfIsProper_eq`: the functor is the restriction
  `boundedConstructibleLowerStar` of Deligne's theorem to proper morphisms (the same lift of the
  same functor, by proof irrelevance), so that every statement about the general functor applies.

The names follow `BoundedConstructibleLowerStarDeligne` with the suffix `OfIsProper`.
-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- The composite of two proper morphisms of `Over (Spec (.of k))` is proper (on the underlying
morphisms of schemes). -/
instance isProper_left_comp {X Y Z : Over (Spec (.of k))} (p : X ⟶ Y) (q : Y ⟶ Z)
    [IsProper p.left] [IsProper q.left] : IsProper (p ≫ q).left :=
  inferInstanceAs (IsProper (p.left ≫ q.left))

/-! ### The coefficient ring `ℚ̲̄_ℓ` -/

section LowerStarOfIsProper

include ℓ k

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : X ⟶ Y) [IsProper p.left]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [IsSeparated Y.hom] in
/-- Proper direct image of constructible complexes: for `p` proper, `Rp_*`
carries bounded constructible complexes of `ℚ̄_ℓ`-sheaves to bounded constructible complexes
(the proper-only finiteness
`boundedConstructible_rightDerivedLowerStar_of_isProper_padicAlgClRingObj_of_finiteType`). -/
lemma boundedConstructible_rightDerivedLowerStar_obj_of_isProper
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)
      ((R((p.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj K.obj) :=
  boundedConstructible_rightDerivedLowerStar_of_isProper_padicAlgClRingObj_of_finiteType ℓ p.left
    Y.hom K.obj K.property

/-- The derived pushforward `Rp_* : Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̲̄_ℓ⟧` along a proper morphism `p` on
bounded constructible complexes: the restriction of `R((p)_*⟦ℚ̲̄_ℓ⟧)`, through the proper-only
finiteness theorem. -/
noncomputable def boundedConstructibleLowerStarOfIsProper :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ R((p.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj_of_isProper ℓ p K

/-- The restricted derived pushforward along a proper morphism is compatible with the inclusions
(`ℚ̄_ℓ`-coefficient). -/
noncomputable def boundedConstructibleLowerStarOfIsProperCompatibility :
    boundedConstructibleLowerStarOfIsProper ℓ p ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((p.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The proper-only functor is the general one restricted to proper morphisms: both are the lift
of `R((p)_*⟦ℚ̲̄_ℓ⟧)` to `Dᵇc`, by proof irrelevance (`ℚ̄_ℓ`-coefficient). -/
@[simp]
lemma boundedConstructibleLowerStarOfIsProper_eq :
    boundedConstructibleLowerStarOfIsProper ℓ p = boundedConstructibleLowerStar ℓ p :=
  rfl

/-- The derived adjunction `Lp^* ⊣ Rp_*` on bounded constructible complexes for `p` proper
(`ℚ̄_ℓ`-coefficient): the restriction of
`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`
along the fully faithful inclusions. -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p ⊣
      boundedConstructibleLowerStarOfIsProper ℓ p :=
  Adjunction.restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) p.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicAlgClRingObj ℓ) ℓ p).symm
    (boundedConstructibleLowerStarOfIsProperCompatibility ℓ p).symm

/-- The derived pushforward along a proper morphism on bounded constructible complexes is a
right adjoint, its left adjoint being `boundedConstructibleUpperStar` (`ℚ̄_ℓ`-coefficient). -/
instance isRightAdjoint_boundedConstructibleLowerStarOfIsProper :
    (boundedConstructibleLowerStarOfIsProper ℓ p).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper ℓ p).isRightAdjoint

/-- The composition isomorphism `Rp_* ⋙ Rq_* ≅ R(p ≫ q)_*` on bounded constructible complexes
for `p`, `q` proper (`ℚ̄_ℓ`-coefficient): the conjugate of `boundedConstructibleUpperStarComp`
under the adjunctions. -/
noncomputable def boundedConstructibleLowerStarOfIsProperComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (q : Y ⟶ Z)
    [IsProper q.left] :
    boundedConstructibleLowerStarOfIsProper ℓ p ⋙ boundedConstructibleLowerStarOfIsProper ℓ q ≅
      boundedConstructibleLowerStarOfIsProper ℓ (p ≫ q) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper ℓ (p ≫ q))
    ((boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper ℓ q).comp
      (boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper ℓ p))
    (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ p q).symm).symm

end LowerStarOfIsProper

/-! ### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj

section LowerStarOfIsProper

include ℓ k

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : X ⟶ Y) [IsProper p.left]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [IsSeparated Y.hom] in
/-- Proper direct image of constructible complexes, clause (1): for `p` proper, `Rp_*`
carries bounded constructible complexes of `E`-sheaves to bounded constructible complexes
(the proper-only finiteness
`boundedConstructible_rightDerivedLowerStar_of_isProper_continuousMapRingObj_of_finiteType`). -/
lemma boundedConstructible_rightDerivedLowerStar_obj_of_isProper
    (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) Y.left)
      ((R((p.left)_*⟦Profinite.continuousMapRingObj E⟧)).obj K.obj) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  exact boundedConstructible_rightDerivedLowerStar_of_isProper_continuousMapRingObj_of_finiteType ℓ
    p.left Y.hom _ K.obj K.property

/-- The derived pushforward `Rp_* : Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y)⟦E̲⟧` along a proper morphism `p` on
bounded constructible complexes: the restriction of `R((p)_*⟦E̲⟧)`, through the proper-only
finiteness theorem. -/
noncomputable def boundedConstructibleLowerStarOfIsProper :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj E⟧ ⥤ Dᵇc(Y.left)⟦Profinite.continuousMapRingObj E⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ R((p.left)_*⟦Profinite.continuousMapRingObj E⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj_of_isProper ℓ E p K

/-- The restricted derived pushforward along a proper morphism is compatible with the inclusions
(`E`-coefficient). -/
noncomputable def boundedConstructibleLowerStarOfIsProperCompatibility :
    boundedConstructibleLowerStarOfIsProper ℓ E p ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((p.left)_*⟦Profinite.continuousMapRingObj E⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The proper-only functor is the general one restricted to proper morphisms (`E`-coefficient). -/
@[simp]
lemma boundedConstructibleLowerStarOfIsProper_eq :
    boundedConstructibleLowerStarOfIsProper ℓ E p = boundedConstructibleLowerStar ℓ E p :=
  rfl

/-- The derived adjunction `Lp^* ⊣ Rp_*` on bounded constructible complexes for `p` proper
(`E`-coefficient). -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper :
    boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ p ⊣
      boundedConstructibleLowerStarOfIsProper ℓ E p :=
  Adjunction.restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E) p.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.continuousMapRingObj E) ℓ p).symm
    (boundedConstructibleLowerStarOfIsProperCompatibility ℓ E p).symm

/-- The derived pushforward along a proper morphism on bounded constructible complexes is a
right adjoint (`E`-coefficient). -/
instance isRightAdjoint_boundedConstructibleLowerStarOfIsProper :
    (boundedConstructibleLowerStarOfIsProper ℓ E p).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper ℓ E p).isRightAdjoint

/-- The composition isomorphism `Rp_* ⋙ Rq_* ≅ R(p ≫ q)_*` on bounded constructible complexes
for `p`, `q` proper (`E`-coefficient). -/
noncomputable def boundedConstructibleLowerStarOfIsProperComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (q : Y ⟶ Z)
    [IsProper q.left] :
    boundedConstructibleLowerStarOfIsProper ℓ E p ⋙ boundedConstructibleLowerStarOfIsProper ℓ E q ≅
      boundedConstructibleLowerStarOfIsProper ℓ E (p ≫ q) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper ℓ E (p ≫ q))
    ((boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper ℓ E q).comp
      (boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper ℓ E p))
    (boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ p q).symm).symm

end LowerStarOfIsProper

end ContinuousMapRingObj

/-! ### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj

section LowerStarOfIsProper

include ℓ k

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : X ⟶ Y) [IsProper p.left]

omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [IsSeparated Y.hom] in
/-- Proper direct image of constructible complexes, clause (1): for `p` proper, `Rp_*`
carries bounded constructible complexes of `𝒪_E`-sheaves to bounded constructible complexes
(the proper-only finiteness
`boundedConstructible_rightDerivedLowerStar_of_isProper_padicIntegersRingObj_of_finiteType`). -/
lemma boundedConstructible_rightDerivedLowerStar_obj_of_isProper
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left)
      ((R((p.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K.obj) :=
  boundedConstructible_rightDerivedLowerStar_of_isProper_padicIntegersRingObj_of_finiteType ℓ p.left
    Y.hom E K.obj K.property

/-- The derived pushforward `Rp_* : Dᵇc(X)⟦𝒪̲_E⟧ ⥤ Dᵇc(Y)⟦𝒪̲_E⟧` along a proper morphism `p` on
bounded constructible complexes: the restriction of `R((p)_*⟦𝒪̲_E⟧)`, through the proper-only
finiteness theorem. -/
noncomputable def boundedConstructibleLowerStarOfIsProper :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤
      Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙ R((p.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧))
    fun K ↦ boundedConstructible_rightDerivedLowerStar_obj_of_isProper ℓ E p K

/-- The restricted derived pushforward along a proper morphism is compatible with the inclusions
(`𝒪_E`-coefficient). -/
noncomputable def boundedConstructibleLowerStarOfIsProperCompatibility :
    boundedConstructibleLowerStarOfIsProper ℓ E p ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ R((p.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧) :=
  ObjectProperty.liftCompιIso _ _ _

/-- The proper-only functor is the general one restricted to proper morphisms
(`𝒪_E`-coefficient). -/
@[simp]
lemma boundedConstructibleLowerStarOfIsProper_eq :
    boundedConstructibleLowerStarOfIsProper ℓ E p = boundedConstructibleLowerStar ℓ E p :=
  rfl

/-- The derived adjunction `Lp^* ⊣ Rp_*` on bounded constructible complexes for `p` proper
(`𝒪_E`-coefficient). -/
noncomputable def boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper :
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p ⊣
      boundedConstructibleLowerStarOfIsProper ℓ E p :=
  Adjunction.restrictFullyFaithful
    (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) p.left)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleUpperStarCompatibility (Profinite.padicIntegersRingObj ℓ E) ℓ p).symm
    (boundedConstructibleLowerStarOfIsProperCompatibility ℓ E p).symm

/-- The derived pushforward along a proper morphism on bounded constructible complexes is a
right adjoint (`𝒪_E`-coefficient). -/
instance isRightAdjoint_boundedConstructibleLowerStarOfIsProper :
    (boundedConstructibleLowerStarOfIsProper ℓ E p).IsRightAdjoint :=
  (boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper ℓ E p).isRightAdjoint

/-- The composition isomorphism `Rp_* ⋙ Rq_* ≅ R(p ≫ q)_*` on bounded constructible complexes
for `p`, `q` proper (`𝒪_E`-coefficient). -/
noncomputable def boundedConstructibleLowerStarOfIsProperComp {Z : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] (q : Y ⟶ Z)
    [IsProper q.left] :
    boundedConstructibleLowerStarOfIsProper ℓ E p ⋙ boundedConstructibleLowerStarOfIsProper ℓ E q ≅
      boundedConstructibleLowerStarOfIsProper ℓ E (p ≫ q) :=
  (conjugateIsoEquiv (boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper ℓ E (p ≫ q))
    ((boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper ℓ E q).comp
      (boundedConstructibleUpperStarLowerStarAdjunctionOfIsProper ℓ E p))
    (boundedConstructibleUpperStarComp (Profinite.padicIntegersRingObj ℓ E) ℓ p q).symm).symm

end LowerStarOfIsProper

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
