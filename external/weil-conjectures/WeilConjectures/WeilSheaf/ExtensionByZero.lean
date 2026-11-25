/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.StalkOpenImmersion
public import WeilConjectures.WeilSheaf.StalkExtensionByZero

/-!
# Extension by zero of Weil sheaves: local Frobenius and upper weight bounds

Let `j : U ⟶ X` be a quasi-compact open immersion. At a closed point of `U` the local Frobenius
of the extension by zero `j₀!F` has the characteristic polynomial of the local Frobenius of `F`
(`AlgebraicGeometry.WeilSheaf.charpoly_frobeniusEnd_stalk_extensionByZero`): the residue fields
agree, and through the comparison `j₀!F ⟶ j₀*F` and the counit of `j̄^* ⊣ j̄_*` so do the
geometric stalks with their Frobenius. Together with the vanishing of the stalks outside `U`
(`AlgebraicGeometry.WeilSheaf.subsingleton_stalk_extensionByZero`), `j₀!` preserves upper weight
bounds (`AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.extensionByZero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

variable [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "j̄" => Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀)))

open scoped ProEtale

/-- The comparison `j₀! F ⟶ j₀* F` on the underlying sheaves, with target `j̄_* F`. -/
noncomputable abbrev extensionByZeroToDirectImageSheaf (F : WeilSheaf k₀ l U) :
    ((extensionByZero j).obj F).obj.carrier.X ⟶
      (j̄)_*[WeilCoefficients.{u} l].obj F.obj.carrier.X :=
  (ProEtale.AdicSheaf.forget _).map ((extensionByZeroToDirectImage j).app F).hom.hom.f

/-- On the underlying sheaves, the pullback along `j̄` of the comparison `j₀! F ⟶ j₀* F` is
invertible: its transpose under `j̄_! ⊣ j̄^*` is the inverse of the counit of `j̄^* ⊣ j̄_*`. -/
instance isIso_upperStar_map_extensionByZeroToDirectImageSheaf (F : WeilSheaf k₀ l U) :
    IsIso ((j̄)^*[WeilCoefficients.{u} l].map (extensionByZeroToDirectImageSheaf j F)) := by
  have h := ProEtale.adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar
    (j̄) F.obj.carrier
  have : IsIso ((j̄)^*ᵃ[l].map
      ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l (j̄)).app F.obj.carrier)) := by
    have : IsIso ((ProEtale.adicOpenImmersionLowerShriekAdjunction l (j̄)).unit.app F.obj.carrier ≫
        (j̄)^*ᵃ[l].map ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l (j̄)).app
          F.obj.carrier)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((ProEtale.adicOpenImmersionLowerShriekAdjunction l (j̄)).unit.app F.obj.carrier) _
  exact (inferInstance : IsIso ((ProEtale.AdicSheaf.forget _).map ((j̄)^*ᵃ[l].map
    ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l (j̄)).app F.obj.carrier))))

omit [Finite k₀] in
/-- The cardinality of the residue field at a closed point is `q ^ deg`. -/
private lemma natCard_residueField_eq_pow {Y : Scheme.{u}} (f : Y.Hom (Spec (.of k₀))) {y : Y}
    (hy : y ∈ Y.finitePoints) : Nat.card (Y.residueField y) = Nat.card k₀ ^ f.degreeOver y := by
  let := (f.residueFieldAlgebraMap y).toAlgebra
  have : Finite (Y.residueField y) := hy
  have : Module.Finite k₀ (Y.residueField y) := Module.Finite.of_finite
  exact Module.natCard_eq_pow_finrank

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact j] in
/-- An open immersion preserves the degrees of the closed points. -/
lemma degreeOver_base_eq (z : U.finitePoints) :
    (X ↘ Spec (CommRingCat.of k₀)).degreeOver (j.base z.1) =
      (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 := by
  have hx := Scheme.Hom.map_mem_finitePoints j z.2
  have e : Nat.card (X.residueField (j.base z.1)) = Nat.card (U.residueField z.1) :=
    Nat.card_congr (asIso (j.residueFieldMap z.1)).commRingCatIsoToRingEquiv.toEquiv
  have hj : j ≫ (X ↘ Spec (CommRingCat.of k₀)) = U ↘ Spec (CommRingCat.of k₀) :=
    comp_over j _
  rw [natCard_residueField_eq_pow (X ↘ Spec (CommRingCat.of k₀)) hx,
    natCard_residueField_eq_pow (U ↘ Spec (CommRingCat.of k₀)) z.2] at e
  exact Nat.pow_right_injective (Finite.one_lt_card (α := k₀)) e

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- The comparison `j₀! F ⟶ j₀* F` is compatible with the Weil structures on the underlying
sheaves. -/
lemma map_extensionByZeroToDirectImageSheaf_comp_frobeniusStr (F : WeilSheaf k₀ l U) :
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map
      (extensionByZeroToDirectImageSheaf j F) ≫ ((lowerStar j).obj F).frobeniusStr =
      ((extensionByZero j).obj F).frobeniusStr ≫ extensionByZeroToDirectImageSheaf j F :=
  map_comp_frobeniusStr ((extensionByZeroToDirectImage j).app F)

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- The map `j̄^* j₀! F ⟶ j̄^* j̄_* F ⟶ F` is compatible with the Weil structures. -/
lemma extensionByZero_stalk_compatible (F : WeilSheaf k₀ l U) :
    (ProEtale.upperStarComp _ (U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom
      (j̄)).hom.app ((extensionByZero j).obj F).obj.carrier.X ≫
        ((U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom)^*[_].map
          ((j̄)^*[_].map (extensionByZeroToDirectImageSheaf j F) ≫
            (ProEtale.upperStarLowerStarAdjunction _ (j̄)).counit.app F.obj.carrier.X) ≫
        F.frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          j (comp_over j (Spec (CommRingCat.of k₀)))).symm).hom.app
          ((extensionByZero j).obj F).obj.carrier.X ≫
        (ProEtale.upperStarComp _ (j̄)
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.hom).hom.app
          ((extensionByZero j).obj F).obj.carrier.X ≫
        (j̄)^*[_].map ((extensionByZero j).obj F).frobeniusStr ≫
        ((j̄)^*[_].map (extensionByZeroToDirectImageSheaf j F) ≫
            (ProEtale.upperStarLowerStarAdjunction _ (j̄)).counit.app F.obj.carrier.X) := by
  rw [map_comp_lowerStar_counit_frobeniusStr_compatible j _
    (map_extensionByZeroToDirectImageSheaf_comp_frobeniusStr j F)]

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- The geometric stalk of `j₀! F` at `t ≫ j̄` is the geometric stalk of `F` at `t`, with its
Frobenius relative to `𝔽_{qᵐ}`. -/
lemma nonempty_equiv_stalkAt_extensionByZero (F : WeilSheaf k₀ l U)
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (U ↘ Spec (CommRingCat.of k₀)).geometricFiber) (m : ℕ)
    (ht : t ≫ ((U ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ t)
    (ht' : (t ≫ j̄) ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ (t ≫ j̄)) :
    Nonempty ((((extensionByZero j).obj F).stalkAt (t ≫ j̄) m ht').Equiv (F.stalkAt t m ht)) :=
  nonempty_equiv_stalkAt_of_upperStar (φ := j) (F := (extensionByZero j).obj F) (G := F)
    (θ := (j̄)^*[_].map (extensionByZeroToDirectImageSheaf j F) ≫
      (ProEtale.upperStarLowerStarAdjunction _ (j̄)).counit.app F.obj.carrier.X)
    (extensionByZero_stalk_compatible j F) t m ht ht'

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- At a closed point of `U`, the local Frobenius of `j₀! F` has the characteristic polynomial
of the local Frobenius of `F`: the residue fields agree, and through the comparison
`j₀! F ⟶ j₀* F` and the counit of `j̄^* ⊣ j̄_*` so do the geometric stalks with their Frobenius. -/
theorem charpoly_frobeniusEnd_stalk_extensionByZero (F : WeilSheaf k₀ l U) (z : U.finitePoints) :
    (((extensionByZero j).obj F).stalk
      ⟨j.base z.1, Scheme.Hom.map_mem_finitePoints j z.2⟩).frobeniusEnd.charpoly =
      (F.stalk z).frobeniusEnd.charpoly := by
  have hdeg := degreeOver_base_eq (k₀ := k₀) j z
  have ht := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (U ↘ Spec (CommRingCat.of k₀)) z
  have ht' : ((U ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint z ≫ j̄) ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
        (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).asIso.hom =
      (specGeometricFrobenius k₀ ^ (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1).asIso.hom ≫
        ((U ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint z ≫ j̄) := by
    rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_pow,
      ← Category.assoc, ht, Category.assoc]
  obtain ⟨e₁⟩ := nonempty_equiv_stalkAt_extensionByZero j F _ _ ht ht'
  have hx : j.base z.1 ∈ X.finitePoints := Scheme.Hom.map_mem_finitePoints j z.2
  have hbase := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
    (X ↘ Spec (CommRingCat.of k₀)) ⟨j.base z.1, hx⟩
  have hss' : (((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint
        ⟨j.base z.1, hx⟩) ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      (((U ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint z ≫ j̄) ≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
          (IsLocalRing.closedPoint (AlgebraicClosure k₀)) := by
    rw [hbase, Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      ← Category.assoc]
    exact (congrArg j.base
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base _ z)).symm
  have hmem : (((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint
        ⟨j.base z.1, hx⟩) ≫ (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) ∈ X.finitePoints := by
    rw [hbase]; exact hx
  have hdvd : (X ↘ Spec (CommRingCat.of k₀)).degreeOver (j.base z.1) ∣
      (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 := by
    rw [hdeg]
  have hc' := ((extensionByZero j).obj F).charpoly_frobeniusEnd_stalkAt_of_dvd _ _ hss' hmem hdvd
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow _
      ⟨j.base z.1, hx⟩) ht'
  have hpos : 0 < (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 :=
    Nat.pos_of_ne_zero (Scheme.Hom.degreeOver_ne_zero _ z.2)
  have hr : (U ↘ Spec (CommRingCat.of k₀)).degreeOver z.1 /
      (X ↘ Spec (CommRingCat.of k₀)).degreeOver (j.base z.1) = 1 := by
    rw [hdeg, Nat.div_self hpos]
  rw [hr, pow_one] at hc'
  exact hc'.symm.trans e₁.charpoly_frobeniusEnd.symm

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- The eigenvalues of the local Frobenius of `j₀! F` at a closed point `x` are those of `F` at
the corresponding point of `U`, and there are none if `x` lies outside `U`. -/
theorem exists_hasEigenvalue_of_hasEigenvalue_stalk_extensionByZero (F : WeilSheaf k₀ l U)
    (x : X.finitePoints) {α : PadicAlgCl l}
    (hα : (((extensionByZero j).obj F).stalk x).frobeniusEnd.HasEigenvalue α) :
    ∃ z : U.finitePoints, j.base z.1 = x.1 ∧ (F.stalk z).frobeniusEnd.HasEigenvalue α ∧
      (X ↘ Spec (CommRingCat.of k₀)).residueCard x.1 =
        (U ↘ Spec (CommRingCat.of k₀)).residueCard z.1 := by
  by_cases hx : x.1 ∈ Set.range j.base
  · obtain ⟨z, hz⟩ := hx
    have hzU : z ∈ U.finitePoints := by
      have : Finite (X.residueField x.1) := x.2
      rw [← hz] at this
      exact Finite.of_equiv _ (asIso (j.residueFieldMap z)).commRingCatIsoToRingEquiv.toEquiv
    obtain rfl : x = ⟨j.base (⟨z, hzU⟩ : U.finitePoints).1,
        Scheme.Hom.map_mem_finitePoints j hzU⟩ := Subtype.ext hz.symm
    refine ⟨⟨z, hzU⟩, rfl, ?_, ?_⟩
    · rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
        charpoly_frobeniusEnd_stalk_extensionByZero,
        ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hα
      exact hα
    · rw [Scheme.Hom.residueCard, Scheme.Hom.residueCard,
        degreeOver_base_eq (k₀ := k₀) j ⟨z, hzU⟩]
  · have := subsingleton_stalk_extensionByZero j F x hx
    obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
    exact absurd (Subsingleton.elim v 0) hv.2

variable {ι : PadicAlgCl l →+* ℂ} {w : ℝ} {F : WeilSheaf k₀ l U}

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] in
/-- Extension by zero along a quasi-compact open immersion preserves upper weight bounds: at a
closed point of `U` the geometric stalk of `j₀!F` is that of `F`, with the same local Frobenius
and the same residue field, and at a closed point outside `U` it vanishes. -/
theorem HasWeightsAtMost.extensionByZero (hF : F.HasWeightsAtMost ι w) :
    ((WeilSheaf.extensionByZero j).obj F).HasWeightsAtMost ι w := by
  intro x α hα
  obtain ⟨z, -, hz, hq⟩ := exists_hasEigenvalue_of_hasEigenvalue_stalk_extensionByZero j F x hα
  rw [hq]
  exact hF z α hz

end WeilSheaf

end AlgebraicGeometry
