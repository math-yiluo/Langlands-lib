/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedLimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedModule
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedProperFree
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal

/-!
# Proper base change in degree zero for twisted sheaves of sets

Let `p : X ⟶ Y` be proper and smooth, `f : V ⟶ X` a pro-étale cover and `c` a descent cocycle on
the constant sheaf `S_V`, defining a pro-étale locally constant sheaf of sets `F_c` on `X`
(`AlgebraicGeometry.IsDescentCocycle`). If `F_c` has a section over every regular Noetherian
`X`-scheme, then every point `y` of `Y` has an affine étale neighbourhood `U` such that `F_c` has
a section over `X ×_Y U` (`AlgebraicGeometry.exists_etale_isTwistedSection_of_isProper`,
blueprint `proposition-proper-base-change-degree-zero`).

The proof follows proper base change in degree zero:
1. over a strictly henselian local ring `A`, a section of `F_c` over the closed geometric fibre
   `Z` of a proper `P ⟶ Spec A` extends to `P`
   (`AlgebraicGeometry.exists_isTwistedSection_of_geometricFibre`): the sections of the sheaf
   `ℤ[F_c]` of free abelian groups over `P` and `Z` agree
   (`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_geometricFibre`), and the locus
   where the extension of `[σ_Z]` is a basis vector is open and closed and descends to a closed
   subset of `P` containing the closed fibre, hence everything, `P ⟶ Spec A` being closed;
2. a section over the base change `X ×_Y Spec 𝒪^{sh}_{Y,s}` to the strict localization comes
   from a section over some `X ×_Y U` for an affine étale neighbourhood `U` of `s`
   (`AlgebraicGeometry.exists_etale_isTwistedSection_of_strictLocalization`), the base change
   being the limit of the `X ×_Y U`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X V : Scheme.{u}} {f : V ⟶ X} {S : Type} {c : ↥(pullback f f) → S → S}

/-- The closed geometric point `Spec κ̄ ⟶ Spec A` of a local ring `A`, for `κ̄` an algebraic
closure of the residue field, maps to the closed point (blueprint
`proposition-proper-base-change-degree-zero`). -/
lemma spec_algebraMap_algebraicClosure_closedPoint (A : Type u) [CommRing A] [IsLocalRing A] :
    (Spec.map (CommRingCat.ofHom (algebraMap A
      (AlgebraicClosure (IsLocalRing.ResidueField A))))).base
        (IsLocalRing.closedPoint (AlgebraicClosure (IsLocalRing.ResidueField A))) =
      IsLocalRing.closedPoint A := by
  have e : algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A)) =
      (algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp
        (IsLocalRing.residue A) := by
    rw [IsScalarTower.algebraMap_eq A (IsLocalRing.ResidueField A),
      IsLocalRing.ResidueField.algebraMap_eq]
  have : IsLocalHom (algebraMap A (AlgebraicClosure (IsLocalRing.ResidueField A))) := by
    rw [e]
    infer_instance
  exact Spec_closedPoint (f := CommRingCat.ofHom _)

/-- **Sections over the closed geometric fibre extend over a strictly henselian base.** Let `A`
be a strictly henselian local ring, `pD : P ⟶ Spec A` proper and `π : P ⟶ X`. A section of the
twisted sheaf of sets defined by `c` over the closed geometric fibre `Z = P ×_A κ̄` extends to a
section over `P`.

The sections of the sheaf of free abelian groups `ℤ[F_c]` over `P` restrict bijectively to those
over `Z` (`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_geometricFibre`); let `τ`
be the extension of `[σ_Z]`. The locus where `τ` is a basis vector descends to an open and
closed subset of `P` (`AlgebraicGeometry.isClopen_image_fiber_of_isLocallyConstant`) containing
`Z`; its complement is closed, with closed image in `Spec A` avoiding the closed point, hence
empty. (blueprint `proposition-proper-base-change-degree-zero`) -/
theorem exists_isTwistedSection_of_geometricFibre [WeaklyEtale f] [Surjective f]
    [QuasiCompact f] [QuasiSeparated f] (hc : IsDescentCocycle f c) (A : Type u) [CommRing A]
    [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] {P : Scheme.{u}}
    (pD : P ⟶ Spec (.of A)) [IsProper pD] (π : P ⟶ X)
    {σ₀ : ↥(pullback f (pullback.fst pD (Spec.map (CommRingCat.ofHom (algebraMap A
      (AlgebraicClosure (IsLocalRing.ResidueField A))))) ≫ π)) → S}
    (hσ₀ : IsTwistedSection f c _ σ₀) :
    ∃ σ, IsTwistedSection f c π σ := by
  classical
  let Λ := ULift.{u + 1} ℤ
  let κ := AlgebraicClosure (IsLocalRing.ResidueField A)
  let sκ : Spec (.of κ) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A κ))
  let q := pullback.fst pD sκ
  have hbij := bijective_twistedRestrict_of_isIso_globalSectionsUpperStarMap
    (hc.freeCocycle Λ) (hc.free Λ) π q
    (Etale.isIso_globalSectionsUpperStarMap_geometricFibre Λ A pD _)
  obtain ⟨τ, hτ⟩ := hbij.2 ⟨fun x ↦ Finsupp.single (σ₀ x) 1, hσ₀.single_one hc Λ⟩
  have hτ' := congrArg Subtype.val hτ
  have hτt : IsTwistedSection f (fun z ↦ ⇑(hc.freeCocycle Λ z)) π τ.1 := τ.2
  let g : ↥(pullback f π) → Prop := fun x ↦ ∃ s, τ.1 x = Finsupp.single s 1
  have hg : IsLocallyConstant g := hτt.1.comp fun m ↦ ∃ s, m = Finsupp.single s 1
  have hginv (w : ↥(pullback (pullback.snd f π) (pullback.snd f π))) :
      g ((pullback.fst (pullback.snd f π) (pullback.snd f π)).base w) =
        g ((pullback.snd (pullback.snd f π) (pullback.snd f π)).base w) := by
    simp only [g]
    rw [hτt.2 w]
    simp only
    rw [IsDescentCocycle.coe_freeCocycle]
    exact propext (exists_mapDomain_eq_single_iff (hc.bijective _) _ _)
  have hB := isClopen_image_fiber_of_isLocallyConstant π g hg hginv False
  have hall (x : ↥(pullback f π)) : g x := by
    by_contra hx
    have hcl : IsClosed (pD.base '' ((pullback.snd f π).base '' (g ⁻¹' {False}))) :=
      pD.isClosedMap _ hB.1
    obtain ⟨b, ⟨x₁, hx₁, rfl⟩, hb⟩ := (IsLocalRing.specializes_closedPoint
      (pD.base ((pullback.snd f π).base x))).mem_closed hcl
        ⟨_, ⟨x, eq_false hx, rfl⟩, rfl⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pD) (g := sκ)
      ((pullback.snd f π).base x₁) (IsLocalRing.closedPoint κ)
      (hb.trans (spec_algebraMap_algebraicClosure_closedPoint A).symm)
    obtain ⟨x', hx', -⟩ := exists_pullbackMapRight_eq q rfl x₁ z hz
    refine of_eq_false hx₁ ⟨σ₀ x', ?_⟩
    rw [← hx']
    exact congrFun hτ' x'
  obtain ⟨σ, hσ, -⟩ := hτt.exists_of_free hc hall
  exact ⟨σ, hσ⟩

/-- The base change `A ×_Y X ⟶ B ×_Y X` of a morphism of `Y`-schemes `φ : A ⟶ B` which is affine
is affine (blueprint `proposition-proper-base-change-degree-zero`). -/
lemma isAffineHom_overPullback_map_left {X Y : Scheme.{u}} (p : X ⟶ Y)
    {A B : CategoryTheory.Over Y} (φ : A ⟶ B) [IsAffineHom φ.left] :
    IsAffineHom ((CategoryTheory.Over.pullback p).map φ).left := by
  have e : ((CategoryTheory.Over.pullback p).map φ).left ≫ pullback.snd B.hom p =
      pullback.snd A.hom p := by
    simp
  have big : IsPullback (((CategoryTheory.Over.pullback p).map φ).left ≫ pullback.snd B.hom p)
      (pullback.fst A.hom p) p (φ.left ≫ B.hom) := by
    rw [e, CategoryTheory.Over.w φ]
    exact (IsPullback.of_hasPullback A.hom p).flip
  have sq := big.of_right (by simp) (IsPullback.of_hasPullback B.hom p).flip
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) sq.flip ‹_›

/-- **Sections over the base change to the strict localization descend to an étale
neighbourhood.** Let `p : X ⟶ Y` be proper and `s : Spec Ω ⟶ Y` a geometric point. A section of
the twisted sheaf of sets defined by `c` over `X ×_Y Spec 𝒪^{sh}_{Y,s}` comes from a section over
`X ×_Y U` for some affine étale neighbourhood `U` of `s`: the base change to the strict
localization is the limit of the `X ×_Y U`
(`AlgebraicGeometry.Scheme.isLimitStrictLocalizationConePullback`), and twisted sections over a
limit come from a finite stage
(`AlgebraicGeometry.IsTwistedSection.exists_of_isLimit`). (blueprint
`proposition-proper-base-change-degree-zero`) -/
theorem exists_etale_isTwistedSection_of_strictLocalization [QuasiCompact f] [QuasiSeparated f]
    (hc : IsDescentCocycle f c) {Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] {Ω : Type u}
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    {σ : ↥(pullback f (pullback.snd (Scheme.strictLocalizationToBase s) p)) → S}
    (hσ : IsTwistedSection f c _ σ) :
    ∃ (U : Scheme.{u}) (j : U ⟶ Y) (v : Spec (.of Ω) ⟶ U), Etale j ∧ IsAffine U ∧ v ≫ j = s ∧
      ∃ σ, IsTwistedSection f c (pullback.fst p j) σ := by
  let J := InitiallySmall.CofilteredInitialModel.{u} (Scheme.AffinePointedEtaleNeighborhood s)
  let ι₀ := InitiallySmall.fromCofilteredInitialModel.{u}
    (Scheme.AffinePointedEtaleNeighborhood s)
  let cK := (CategoryTheory.Over.forget X).mapCone
    ((CategoryTheory.Over.pullback p).mapCone (Scheme.strictLocalizationConeOver s))
  have hC : IsLimit (cK.whisker ι₀) := (Functor.Initial.isLimitWhiskerEquiv ι₀ cK).symm
    (Scheme.isLimitStrictLocalizationConePullback s p)
  have hcpt (j : J) : CompactSpace ((ι₀ ⋙ (Scheme.affineNeighborhoodDiagramOver s ⋙
      CategoryTheory.Over.pullback p) ⋙ CategoryTheory.Over.forget X).obj j) := by
    have : CompactSpace ((𝟭 Scheme).obj (ι₀.obj j).obj.1.left) :=
      inferInstanceAs (CompactSpace (ι₀.obj j).obj.1.left)
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst (ι₀.obj j).obj.1.hom p)
  have hqs (j : J) : QuasiSeparatedSpace ((ι₀ ⋙ (Scheme.affineNeighborhoodDiagramOver s ⋙
      CategoryTheory.Over.pullback p) ⋙ CategoryTheory.Over.forget X).obj j) := by
    have : QuasiSeparatedSpace ((𝟭 Scheme).obj (ι₀.obj j).obj.1.left) :=
      inferInstanceAs (QuasiSeparatedSpace (ι₀.obj j).obj.1.left)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (ι₀.obj j).obj.1.hom p)
  have haff {i j : J} (g : i ⟶ j) : IsAffineHom ((ι₀ ⋙ (Scheme.affineNeighborhoodDiagramOver s ⋙
      CategoryTheory.Over.pullback p) ⋙ CategoryTheory.Over.forget X).map g) := by
    have : IsAffine ((Scheme.affineNeighborhoodDiagramOver s).obj (ι₀.obj i)).left := (ι₀.obj i).2
    have : IsAffine ((Scheme.affineNeighborhoodDiagramOver s).obj (ι₀.obj j)).left := (ι₀.obj j).2
    have : IsAffineHom ((Scheme.affineNeighborhoodDiagramOver s).map (ι₀.map g)).left :=
      isAffineHom_of_isAffine _
    exact isAffineHom_overPullback_map_left p _
  obtain ⟨j, σⱼ, hσⱼ, -⟩ := IsTwistedSection.exists_of_isLimit hc hC
    (fun j ↦ ((CategoryTheory.Over.pullback p).obj
      ((Scheme.affineNeighborhoodDiagramOver s).obj (ι₀.obj j))).hom)
    (fun g ↦ CategoryTheory.Over.w ((CategoryTheory.Over.pullback p).map
      ((Scheme.affineNeighborhoodDiagramOver s).map (ι₀.map g))))
    (pullback.snd (Scheme.strictLocalizationToBase s) p)
    (fun j ↦ CategoryTheory.Over.w ((CategoryTheory.Over.pullback p).map
      ((Scheme.strictLocalizationConeOver s).π.app (ι₀.obj j)))) hσ
  let N := ι₀.obj j
  refine ⟨N.obj.1.left, N.obj.1.hom, N.obj.2.left, N.obj.1.prop, N.2,
    CategoryTheory.Over.w N.obj.2, _, hσⱼ.comp (pullbackSymmetry p N.obj.1.hom).hom
      (pullbackSymmetry_hom_comp_snd p N.obj.1.hom)⟩

/-- **Proper base change in degree zero for twisted sheaves of sets, in étale-local form.** Let
`p : X ⟶ Y` be proper and smooth, `f : V ⟶ X` weakly étale, surjective, quasi-compact and
quasi-separated, and `c` a descent cocycle on the constant sheaf `S_V`. If the twisted sheaf of
sets `F_c` on `X` has a section over every regular, locally Noetherian, quasi-compact
`X`-scheme, then every point `y` of `Y` has an affine étale neighbourhood `j : U ⟶ Y` such that
`F_c` has a section over `X ×_Y U`.

Let `s` be the geometric point at an algebraic closure of `κ(y)` and `D = Spec 𝒪^{sh}_{Y,s}`
the strict localization. The closed geometric fibre `Z` of the proper `X ×_Y D ⟶ D` is smooth
over a field, hence regular, Noetherian and quasi-compact, so `F_c` has a section over `Z`; it
extends to `X ×_Y D` (`AlgebraicGeometry.exists_isTwistedSection_of_geometricFibre`), and comes
from some `X ×_Y U` (`AlgebraicGeometry.exists_etale_isTwistedSection_of_strictLocalization`).
Smoothness of `p` is only used to make `Z` regular. (blueprint
`proposition-proper-base-change-degree-zero`) -/
theorem exists_etale_isTwistedSection_of_isProper {X Y V : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    [Smooth p] (f : V ⟶ X) [WeaklyEtale f] [Surjective f] [QuasiCompact f] [QuasiSeparated f]
    {S : Type} {c : ↥(pullback f f) → S → S} (hc : IsDescentCocycle f c)
    (hZ : ∀ (Z : Scheme.{u}) (π : Z ⟶ X), IsRegular Z → IsLocallyNoetherian Z → CompactSpace Z →
      ∃ σ, IsTwistedSection f c π σ)
    (y : Y) :
    ∃ (U : Scheme.{u}) (j : U ⟶ Y), Etale j ∧ IsAffine U ∧ y ∈ Set.range j.base ∧
      ∃ σ, IsTwistedSection f c (pullback.fst p j) σ := by
  let κ := AlgebraicClosure (Y.residueField y)
  let s : Spec (.of κ) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) κ)) ≫ Y.fromSpecResidueField y
  let A := Scheme.strictHenselization s
  let pD := pullback.fst (Scheme.strictLocalizationToBase s) p
  let sκ : Spec (.of (AlgebraicClosure (IsLocalRing.ResidueField A))) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A _))
  obtain ⟨σ₀, hσ₀⟩ := hZ _ (pullback.fst pD sκ ≫ pullback.snd (Scheme.strictLocalizationToBase s) p)
    (IsRegular.of_smooth (pullback.snd pD sκ)) inferInstance
    (QuasiCompact.compactSpace_of_compactSpace (pullback.snd pD sκ))
  obtain ⟨σD, hσD⟩ := exists_isTwistedSection_of_geometricFibre hc A pD _ hσ₀
  obtain ⟨U, j, v, hj, hU, hv, σ, hσ⟩ :=
    exists_etale_isTwistedSection_of_strictLocalization hc p s hσD
  refine ⟨U, j, hj, hU, ⟨v.base (IsLocalRing.closedPoint κ), ?_⟩, σ, hσ⟩
  rw [← Scheme.Hom.comp_apply, hv, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply (X := Y) y _

end AlgebraicGeometry
