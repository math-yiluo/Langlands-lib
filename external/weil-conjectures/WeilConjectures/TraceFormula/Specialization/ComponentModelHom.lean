/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SupportCompactSupportExchange

/-!
# The morphism of deformation models over a component of the fixed locus

Let `c` be contracting at `y`, `F` a fixed locus of `c` and `j : B ⟶ F` with a rational point `b`
of `B` over `y`. The closed embedding `B ⊂ F ⊂ C` induces a morphism of deformation models
`𝒟_B ⟶ 𝒞` (`componentModelHom`), whose morphism of total spaces is a closed immersion when
`B ⊂ C` is closed (`isClosedImmersion_componentModelHom_total`). Its properness and the
compact-support exchange on `B` are in
`WeilConjectures.TraceFormula.Specialization.SupportExchangeOnComponent`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace Correspondence.IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [Algebra k k']
  {F : c.FixedLocus} {B : Over (Spec (.of k))} (j : B ⟶ F.F) {b : RationalPoint B}
  (hb : b ≫ j ≫ F.ι = y)

include hb in
/-- Functions vanishing at `y` pull back along `B ⊂ F ⊂ C` to functions vanishing at `b`. -/
lemma map_siteIdeal_le_ker_component :
    ∀ ⦃U' : B.left.AffineZariskiSite⦄ ⦃U : c.C.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ (j ≫ F.ι).left ⁻¹ᵁ U.1),
      (y.left.ker.siteIdeal U).map ((j ≫ F.ι).left.appLE U.1 U'.1 hU).hom ≤
        b.left.ker.siteIdeal U' := by
  refine IdealSheafData.map_siteIdeal_le_of_comap_le _ ?_
  rw [IdealSheafData.comap_le_ker_iff, ← Over.comp_left, hb]

/-- The morphism of deformation models `𝒟_B ⟶ 𝒞` over `B ⊂ F ⊂ C` (`ι ∘ j`), for the deformations
of `B` along `ker b` and of `C` along `ker y`. -/
noncomputable def componentModelHom :=
  deformationModelHom (j ≫ F.ι) (map_siteIdeal_le_ker_component j hb) k'

include hb in
/-- The preimage of `y` under the closed immersion `B ⊂ F ⊂ C` is the point `b`. -/
lemma comap_ker_component [IsClosedImmersion (j ≫ F.ι).left] :
    y.left.ker.comap (j ≫ F.ι).left = b.left.ker := by
  have : IsClosedImmersion y.left := isClosedImmersion_of_comp_eq_id c.C.hom y.left (Over.w y)
  have hP : IsPullback b.left (𝟙 _) (j ≫ F.ι).left y.left :=
    (IsPullback.of_horiz_isIso_mono (fst := 𝟙 _) (snd := b.left)
      ⟨by rw [Category.id_comp, ← Over.comp_left, hb]⟩).flip
  rw [← IdealSheafData.ker_fst_of_isClosedImmersion, ← hP.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

include hb in
/-- If `B ⊂ F ⊂ C` is a closed immersion, so is the morphism of total spaces of
`componentModelHom`: the deformation space of `B` along `ker b = (ker y)|_B` is closed in that of
`C` (`IdealSheafData.isClosedImmersion_deformationSpaceMap`). -/
lemma isClosedImmersion_componentModelHom_total [IsClosedImmersion (j ≫ F.ι).left] :
    IsClosedImmersion (componentModelHom k' j hb).total :=
  have := IdealSheafData.isClosedImmersion_deformationSpaceMap (j ≫ F.ι).left y.left.ker
    b.left.ker (map_siteIdeal_le_ker_component j hb) (comap_ker_component j hb).symm
  MorphismProperty.of_isPullback
    (isPullback_deformationTotalMap (j ≫ F.ι) (map_siteIdeal_le_ker_component j hb) k').flip this

end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing
