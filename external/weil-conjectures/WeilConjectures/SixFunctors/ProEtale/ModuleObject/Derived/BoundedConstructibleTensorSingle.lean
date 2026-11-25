/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.LfpTensorSingle
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Derived tensor product of constructible sheaves in degree zero -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

/-- Let `Λ` be a condensed ring such that, on every noetherian scheme, the derived tensor product of
two locally finitely presented `Λ`-module sheaves placed in degree `0` has no cohomology below
degree `-1` and locally finitely presented cohomology sheaves. Then the derived tensor product of
two constructible sheaves placed in degree `0` is bounded constructible (the reduction step of the
case of single sheaves in blueprint `proposition-six-operations-dctf--14`).

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3).

Proof: the finite-type scheme is noetherian. Refine the constructible stratifications of `F`
and `G` to a common one on whose strata both restrictions are locally finitely presented.
Pullback to a stratum is monoidal and exact, so it identifies the restriction of `F ⊗ᴸ G`
with the derived tensor product of the restrictions, to which the hypothesis applies. The derived
tensor product of complexes concentrated in degrees `≤ 0` is concentrated in degrees `≤ 0`. The
strata detect vanishing, so the bounds descend, and the common stratification exhibits every
cohomology sheaf as constructible. -/
theorem boundedConstructible_tensor_single_of_lfp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {k : Type u} [Field k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (hlfp : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (F G : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) F →
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) G →
      ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G).IsGE (-1) ∧
      ∀ n : ℤ, IsLocallyFinitelyPresented (condensedRingObj Λ Y)
        ((DerivedCategory.homologyFunctor _ n).obj
          ((DerivedCategory.singleFunctor _ 0).obj F ⊗
            (DerivedCategory.singleFunctor _ 0).obj G)))
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))
    (hF : IsConstructibleModuleObject (condensedRingObj Λ X.left) F)
    (hG : IsConstructibleModuleObject (condensedRingObj Λ X.left) G) :
    boundedConstructible (condensedRingObj Λ X.left)
      (((-⊗ᴸ-(X.left)⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj F)).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) := by
  change boundedConstructible _ ((DerivedCategory.singleFunctor _ 0).obj F ⊗
    (DerivedCategory.singleFunctor _ 0).obj G)
  classical
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  let R := condensedRingObj Λ X.left
  let K := (DerivedCategory.singleFunctor _ 0).obj F ⊗
    (DerivedCategory.singleFunctor _ 0).obj G
  obtain ⟨S, hS⟩ := common_lfp_stratification hF hG
  let H (a : Fin S.n) := upperStar Λ (S.immersion a)
  have lfp (a : Fin S.n)
      (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) R)
      (hM : IsLocallyFinitelyPresented
        ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj R)
        (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).obj M)) :
      IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a)) ((H a).obj M) := by
    exact localFinitePresentation_of_iso
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (S.immersion a))).app _).symm
      (localFinitePresentation_comap _ hM)
  let e (a : Fin S.n) : (H a).leftDerivedFunctor.obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj ((H a).obj F) ⊗
        (DerivedCategory.singleFunctor _ 0).obj ((H a).obj G) :=
    (Functor.Monoidal.μIso (H a).leftDerivedFunctor _ _).symm ≪≫
      tensorIso ((H a).singleFunctorCompLeftDerivedFunctorIso.app F)
        ((H a).singleFunctorCompLeftDerivedFunctorIso.app G)
  have hlocal (a : Fin S.n) :
      TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.noetherianSpace
  have hom_lfp (a : Fin S.n) (n : ℤ) :
      IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a))
        ((H a).obj ((DerivedCategory.homologyFunctor _ n).obj K)) := by
    apply localFinitePresentation_of_iso
      ((H a).leftDerivedFunctorHomologyFunctorIso n |>.app K).symm
    apply localFinitePresentation_of_iso ((DerivedCategory.homologyFunctor _ n).mapIso (e a)).symm
    exact (hlfp (S.domain a) ((H a).obj F) ((H a).obj G)
      (lfp a F (hS a).1) (lfp a G (hS a).2)).2 n
  have detect
      (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) R)
      (hM : ∀ a : Fin S.n, IsZero ((H a).obj M)) : IsZero M := by
    rw [IsZero.iff_id_eq_zero]
    apply Mod.hom_ext
    apply eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp S.immersion
    · intro x
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
      exact ⟨a, S.range_immersion a |>.symm ▸ ha⟩
    · intro a
      let e' := (Mod.extendScalarsIsoComapInv
        (condensedPullbackHom Λ (S.immersion a))).app
        (((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).mapMod R).obj M)
      have hz := (Mod.forget _).map_isZero ((hM a).of_iso e'.symm)
      change IsZero ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).obj M.X) at hz
      simpa using hz.eq_of_src
        ((ProEtale.upperStar Ab.{u + 1} (S.immersion a)).map (𝟙 M.X)) 0
  have hupper := DerivedCategory.isLE_tensor
    ((DerivedCategory.singleFunctor _ 0).obj F)
    ((DerivedCategory.singleFunctor _ 0).obj G) 0 0
  rw [add_zero] at hupper
  apply (mem_boundedConstructible_iff R K).2
  constructor
  · refine ⟨-1, 0, fun n hn ↦ ?_⟩
    rcases hn with hn | hn
    · apply detect
      intro a
      have hb := (hlfp (S.domain a) ((H a).obj F) ((H a).obj G)
        (lfp a F (hS a).1) (lfp a G (hS a).2)).1
      have hz := (DerivedCategory.isGE_iff _ (-1)).1 hb n hn
      exact hz.of_iso
        (((H a).leftDerivedFunctorHomologyFunctorIso n).app K ≪≫
          (DerivedCategory.homologyFunctor _ n).mapIso (e a))
    · exact (DerivedCategory.isLE_iff K 0).1 hupper n hn
  · intro n
    refine ⟨S, fun a ↦ ?_⟩
    apply localFinitePresentation_of_comap (inv (condensedPullbackHom Λ (S.immersion a)))
    apply localFinitePresentation_of_iso
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ (S.immersion a))).app _)
    exact hom_lfp a n

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

/-! ### The coefficient ring `ℚ̲̄_ℓ` -/

/-- The derived tensor product of two constructible `ℚ̄_ℓ`-sheaves placed in degree `0` is bounded
constructible. This is the case of single sheaves in blueprint
`proposition-six-operations-dctf--14`.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3).

Proof: `boundedConstructible_tensor_single_of_lfp`, with the local calculation
`lfp_tensor_single_padicAlgClRingObj` (local freeness). -/
theorem boundedConstructible_tensor_single
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) F)
    (hG : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) G) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)
      (((-⊗ᴸ-(X.left)⟦(Profinite.padicAlgClRingObj ℓ)⟧).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) :=
  boundedConstructible_tensor_single_of_lfp _ X
    (fun Y _ ↦ lfp_tensor_single_padicAlgClRingObj ℓ Y) F G hF hG

/-! ### The coefficient ring `E̲`, `E ⊆ ℚ̄_ℓ` a finite subextension of `ℚ_ℓ` -/

namespace ContinuousMapRingObj

/-- For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the derived tensor product of two constructible
`E`-sheaves placed in degree `0` is bounded constructible. This is the case of single
sheaves in blueprint `proposition-six-operations-dctf--14`.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3).

Proof: `boundedConstructible_tensor_single_of_lfp`, with the local calculation
`lfp_tensor_single_continuousMapRingObj` (local freeness). -/
theorem boundedConstructible_tensor_single (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left) F)
    (hG : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left) G) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X.left)
      (((-⊗ᴸ-(X.left)⟦(Profinite.continuousMapRingObj E)⟧).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) :=
  boundedConstructible_tensor_single_of_lfp _ X
    (fun Y _ ↦ lfp_tensor_single_continuousMapRingObj ℓ Y E) F G hF hG

end ContinuousMapRingObj

/-! ### The coefficient ring `𝒪̲_E`, `E ⊆ ℚ̄_ℓ` a finite extension of `ℚ_ℓ` -/

namespace PadicIntegersRingObj

/-- For a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, the derived tensor product of two constructible
`𝒪_E`-sheaves placed in degree `0` is bounded constructible. This is the case of single
sheaves in blueprint `proposition-six-operations-dctf--14`.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3).

Proof: `boundedConstructible_tensor_single_of_lfp`, with the local calculation
`lfp_tensor_single_padicIntegersRingObj` (a two-term locally finite free resolution). -/
theorem boundedConstructible_tensor_single (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) F)
    (hG : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) G) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)
      (((-⊗ᴸ-(X.left)⟦(Profinite.padicIntegersRingObj ℓ E)⟧).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) :=
  boundedConstructible_tensor_single_of_lfp _ X
    (fun Y _ ↦ lfp_tensor_single_padicIntegersRingObj ℓ Y E) F G hF hG

end PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
