/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.WContractibleDisjointCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective

/-!
# Pro-étale covers over which the unit is projective

* Over the spectrum of a w-contractible ring, the unit of abelian pro-étale sheaves is projective
  (`AlgebraicGeometry.ProEtale.projective_tensorUnit_of_isWContractibleRing`).
* Every scheme has a pro-étale cover by spectra of w-contractible rings, indexed by a type in the
  universe of the scheme (`AlgebraicGeometry.Scheme.exists_cover_projective_tensorUnit`), over
  which the unit of abelian sheaves is therefore projective.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

/-- Over the spectrum of a w-contractible ring, the unit of abelian pro-étale sheaves is
projective: the final object is weakly contractible. -/
lemma projective_tensorUnit_of_isWContractibleRing (R : CommRingCat.{u}) [IsWContractibleRing R] :
    Projective (𝟙_ (Sheaf (Scheme.ProEt.topology (Spec R)) AddCommGrpCat.{u + 1})) :=
  Projective.of_iso
    (asIso (Functor.LaxMonoidal.ε (presheafToSheaf (Scheme.ProEt.topology (Spec R))
      AddCommGrpCat.{u + 1}))).symm
    (projective_presheafToSheaf_const (Scheme.ProEt.isTerminalMkId _)
      (Scheme.ProEt.isWeaklyContractible_of_iso (W := Scheme.ProEt.mk (𝟙 (Spec R))) (R := R)
        (Iso.refl _)))

end ProEtale

/-- **Every scheme has a pro-étale cover over whose members the unit is projective**: cover `X`
by affine opens `Spec A`, and each `Spec A` by `Spec B` for a faithfully flat, ind-étale,
w-contractible `A`-algebra `B`. -/
theorem Scheme.exists_cover_projective_tensorUnit (X : Scheme.{u}) :
    ∃ 𝒰 : X.Cover.{u} Scheme.proetalePrecoverage, ∀ i,
      Projective (𝟙_ (Sheaf (Scheme.ProEt.topology (𝒰.X i)) AddCommGrpCat.{u + 1})) := by
  have 𝒜 : X.AffineOpenCover := X.affineOpenCover
  choose S iS iA hind hff hw using fun x : 𝒜.I₀ ↦ exists_isWContractibleRing (𝒜.X x)
  let φ (x : 𝒜.I₀) : 𝒜.X x ⟶ CommRingCat.of (S x) := CommRingCat.ofHom (algebraMap _ _)
  have (x : 𝒜.I₀) : WeaklyEtale (Spec.map (φ x)) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 (hind x))
  have (x : 𝒜.I₀) : Surjective (Spec.map (φ x)) :=
    ((flat_and_surjective_SpecMap_iff (φ x)).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 (hff x))).2
  let 𝒰₀ : X.Cover.{u} Scheme.proetalePrecoverage :=
    𝒜.openCover.weaken zariskiPrecoverage_le_proetalePrecoverage
  let 𝒱 (x : 𝒜.I₀) : (𝒰₀.X x).Cover.{u} Scheme.proetalePrecoverage :=
    Precoverage.ZeroHypercover.singleton (Spec.map (φ x))
      (Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (f := Spec.map (φ x))
        inferInstance)
  refine ⟨𝒰₀.bind 𝒱, fun i ↦ ?_⟩
  have := hw i.1
  exact ProEtale.projective_tensorUnit_of_isWContractibleRing (CommRingCat.of (S i.1))

end AlgebraicGeometry
