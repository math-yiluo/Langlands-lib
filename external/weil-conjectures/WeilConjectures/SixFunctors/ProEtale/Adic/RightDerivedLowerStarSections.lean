/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarColimit
public import WeilConjectures.SixFunctors.ProEtale.UpperStarSectionsFilteredColimit

/-!
# Sections of `p^* Rⁱg_* ℚ̄_ℓ,T` over qcqs objects

Let `g : T ⟶ Y` be quasi-compact and quasi-separated, `p : S ⟶ Y` any morphism and `W` an
object of the pro-étale site of `S` with quasi-compact quasi-separated underlying space. Write
`Φ = Γ(W, p^* Rⁱg_* -)` for abelian sheaves on `T_proét`. Since
`ℚ̄_ℓ,T = colim_E colim_n (𝒪_{E,T} --ℓ--> 𝒪_{E,T} --ℓ--> ⋯)` and `Rⁱg_*`, `p^*` and `Γ(W, -)`
commute with filtered colimits, every element of `Φ(ℚ̄_ℓ,T)` is the image of an element `y` of
`Φ(𝒪_{E,T})` under the map `ℓ⁻ⁿ : 𝒪_{E,T} ⟶ ℚ̄_ℓ,T` for some finite `E ⊆ ℚ̄_ℓ` and `n`
(`AlgebraicGeometry.ProEtale.exists_sections_adicConstantSheafLeg_eq`, and with `E` containing
a given `E₀`: `AlgebraicGeometry.ProEtale.exists_sections_adicConstantSheafLeg_eq_of_le`), and
`y` maps to zero iff
`ℓᵐ y` vanishes in `Φ(𝒪_{F,T})` for some finite `F ⊇ E` and some `m`
(`AlgebraicGeometry.ProEtale.exists_pow_smul_map_eq_zero_of_adicConstantSheafLeg`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite PadicAlgCl

namespace AlgebraicGeometry.ProEtale

open Scheme Scheme.ProEt

section IntegersMap

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]
  {E F : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : E ≤ F)

/-- The inclusion `𝒪_E ⟶ 𝒪_F` for subextensions `E ⊆ F` of `ℚ̄_ℓ`. -/
noncomputable def integersInclusion : integers l E →+* integers l F :=
  ((IntermediateField.inclusion h).toRingHom.comp (integers l E).subtype).codRestrict _
    fun x ↦ x.2

lemma continuous_integersInclusion :
    letI := normedFieldOfAlgebra l E
    letI := normedFieldOfAlgebra l F
    Continuous (integersInclusion l h) :=
  letI := normedFieldOfAlgebra l E
  letI := normedFieldOfAlgebra l F
  Continuous.subtype_mk (f := fun x : integers l E ↦ IntermediateField.inclusion h (x : E))
    ((continuous_induced_rng (f := algebraMap F (PadicAlgCl l))).mpr
      (show Continuous fun x : integers l E ↦ algebraMap E (PadicAlgCl l) (x : E) from
        continuous_induced_dom.comp continuous_subtype_val)) _

/-- The inclusion `𝒪_{E,X} ⟶ 𝒪_{F,X}` for subextensions `E ⊆ F` of `ℚ̄_ℓ`. -/
noncomputable def padicIntegersSheafMapOfLE :
    padicIntegersSheaf X l E ⟶ padicIntegersSheaf X l F :=
  letI := normedFieldOfAlgebra l E
  letI := normedFieldOfAlgebra l F
  continuousMapRingSheafMap X (integersInclusion l h) (continuous_integersInclusion l h)

/-- The maps `ℓ⁻ⁿ : 𝒪_{E,X} ⟶ E_X` commute with the inclusions for `E ⊆ F`. -/
lemma padicSubfieldSheafCocone_ι_comp_mapOfLE (n : ℕ) :
    (padicSubfieldSheafCocone X l E).ι.app n ≫
        (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (padicSubfieldSheafMapOfLE X l h) =
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (padicIntegersSheafMapOfLE X l h) ≫ (padicSubfieldSheafCocone X l F).ι.app n := by
  ext U f
  refine congrArg ULift.up (ContinuousMap.ext fun x ↦ Subtype.ext ?_)
  change ((((l : E) ^ n)⁻¹ * (f.down x : E) : E) : PadicAlgCl l) =
    ((((l : F) ^ n)⁻¹ * (integersInclusion l h (f.down x) : F) : F) : PadicAlgCl l)
  push_cast
  rfl

variable {X l} in
/-- The transition maps of `𝒪_{E,X} --ℓ--> 𝒪_{E,X} --ℓ--> ⋯` are multiplication by powers
of `ℓ`. -/
lemma padicIntegersSheafMulSequence_map_homOfLE (E : Type) [Field E] [Algebra E (PadicAlgCl l)]
    (n m : ℕ) :
    letI := normedFieldOfAlgebra l E
    (padicIntegersSheafMulSequence X l E).map (homOfLE (n.le_add_right m)) = (l ^ m) • 𝟙 _ := by
  let := normedFieldOfAlgebra l E
  induction m with
  | zero => exact (CategoryTheory.Functor.map_id _ _).trans (one_smul _ _).symm
  | succ m ih =>
    have e : (homOfLE (n.le_add_right (m + 1)) : n ⟶ n + (m + 1)) =
        homOfLE (n.le_add_right m) ≫ homOfLE ((n + m).le_add_right 1) := rfl
    rw [e, Functor.map_comp, ih, padicIntegersSheafMulSequence_map_succ, Preadditive.nsmul_comp,
      Category.id_comp, pow_succ, mul_smul]
    congr 1
    ext U f
    refine congrArg ULift.up (ContinuousMap.ext fun x ↦ ?_)
    change (l : integers l E) * f.down x = l • f.down x
    rw [nsmul_eq_mul]

end IntegersMap

variable {T Y S : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g] [QuasiSeparated g] (p : S ⟶ Y)
  (i : ℕ) (W : S.ProEt) [CompactSpace W.left] [QuasiSeparatedSpace W.left]
  (l : ℕ) [Fact l.Prime]

/-- `Γ(W, p^* Rⁱg_* -)` on abelian sheaves on `T_proét`. -/
noncomputable abbrev upperStarRightDerivedSections :
    Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  (ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived i ⋙
    (p)^*[AddCommGrpCat.{u + 1}] ⋙ abSectionsFunctor W

variable (T) in
/-- The map `ℓ⁻ⁿ : 𝒪_{E,T} ⟶ E_T ⟶ ℚ̄_ℓ,T` of abelian sheaves. -/
noncomputable def adicConstantSheafLeg (E : FiniteIntermediateField l) (n : ℕ) :
    (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf T l E.1) ⟶
      (sheafCompose (ProEt.topology T) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj
        (adicConstantSheaf l T) :=
  (padicSubfieldSheafCocone T l E.1).ι.app n ≫
    ((padicAlgClSheafCocone T l).extend (padicAlgClSheafIsoAdicConstantSheaf T l).hom).ι.app E

/-- `Γ(W, p^* Rⁱg_* ℚ̄_ℓ,T) = colim_E Γ(W, p^* Rⁱg_* E_T)`. -/
noncomputable def isColimitUpperStarRightDerivedSectionsAdicConstantSheaf :
    IsColimit ((upperStarRightDerivedSections g p i W).mapCocone
      ((padicAlgClSheafCocone T l).extend (padicAlgClSheafIsoAdicConstantSheaf T l).hom)) :=
  isColimitSectionsOfIsColimitOfSmall (isColimitOfPreserves (p)^*[AddCommGrpCat.{u + 1}]
    (isColimitRightDerivedLowerStarAdicConstantSheafCocone g l i)) W

/-- `Γ(W, p^* Rⁱg_* E_T) = colim_n Γ(W, p^* Rⁱg_* 𝒪_{E,T})` along multiplication by `ℓ`. -/
noncomputable def isColimitUpperStarRightDerivedSectionsPadicSubfieldSheaf (E : Type) [Field E]
    [Algebra E (PadicAlgCl l)] :
    letI := normedFieldOfAlgebra l E
    IsColimit ((upperStarRightDerivedSections g p i W).mapCocone
      (padicSubfieldSheafCocone T l E)) :=
  letI := normedFieldOfAlgebra l E
  isColimitSectionsOfIsColimitOfSmall (isColimitOfPreserves (p)^*[AddCommGrpCat.{u + 1}]
    (isColimitRightDerivedLowerStarPadicSubfieldSheafCocone g l E i)) W

/-- **Every section of `p^* Rⁱg_* ℚ̄_ℓ,T` over a qcqs `W` is `ℓ⁻ⁿ y`** for a section `y` of
`p^* Rⁱg_* 𝒪_{E,T}`, `E ⊆ ℚ̄_ℓ` finite over `ℚ_ℓ`. -/
theorem exists_sections_adicConstantSheafLeg_eq
    (s : (upperStarRightDerivedSections g p i W).obj
      ((sheafCompose (ProEt.topology T) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj
        (adicConstantSheaf l T))) :
    ∃ (E : FiniteIntermediateField l) (n : ℕ)
      (y : (upperStarRightDerivedSections g p i W).obj
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf T l E.1))),
      (upperStarRightDerivedSections g p i W).map (adicConstantSheafLeg T l E n) y = s := by
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits
    (CategoryTheory.forget Ab.{u + 1})
  obtain ⟨E, s', rfl⟩ := Concrete.isColimit_exists_rep _
    (isColimitUpperStarRightDerivedSectionsAdicConstantSheaf g p i W l) s
  obtain ⟨n, y, rfl⟩ := Concrete.isColimit_exists_rep _
    (isColimitUpperStarRightDerivedSectionsPadicSubfieldSheaf g p i W l E.1) s'
  refine ⟨E, n, y, ?_⟩
  rw [adicConstantSheafLeg, Functor.map_comp, ConcreteCategory.comp_apply]
  rfl

/-- **Vanishing of `ℓ⁻ⁿ y` in `p^* Rⁱg_* ℚ̄_ℓ,T` over a qcqs `W`**: if `y`, a section of
`p^* Rⁱg_* 𝒪_{E,T}`, maps to zero, then `ℓᵐ y` vanishes in `p^* Rⁱg_* 𝒪_{F,T}` for some finite
`F ⊇ E` and some `m`. -/
theorem exists_pow_smul_map_eq_zero_of_adicConstantSheafLeg {E : FiniteIntermediateField l}
    {n : ℕ} (y : (upperStarRightDerivedSections g p i W).obj
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf T l E.1)))
    (hy : (upperStarRightDerivedSections g p i W).map (adicConstantSheafLeg T l E n) y = 0) :
    ∃ (F : FiniteIntermediateField l) (h : E.1 ≤ F.1) (m : ℕ),
      l ^ m • (upperStarRightDerivedSections g p i W).map
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (padicIntegersSheafMapOfLE T l h)) y = 0 := by
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits
    (CategoryTheory.forget Ab.{u + 1})
  let Φ := upperStarRightDerivedSections g p i W
  rw [adicConstantSheafLeg, Functor.map_comp, ConcreteCategory.comp_apply] at hy
  obtain ⟨F, f, _, hf⟩ := Concrete.isColimit_exists_of_rep_eq (i := E) (j := E) _
    (isColimitUpperStarRightDerivedSectionsAdicConstantSheaf g p i W l) _
    (0 : ToType (Φ.obj _)) (hy.trans (map_zero _).symm)
  rw [map_zero] at hf
  have h := leOfHom f
  have hc := ConcreteCategory.congr_hom
    (congrArg Φ.map (padicSubfieldSheafCocone_ι_comp_mapOfLE T l h n)) y
  rw [Functor.map_comp, Functor.map_comp] at hc
  have hf' := hc.symm.trans hf
  obtain ⟨k, a, _, ha⟩ := Concrete.isColimit_exists_of_rep_eq (i := n) (j := n) _
    (isColimitUpperStarRightDerivedSectionsPadicSubfieldSheaf g p i W l F.1) _
    (0 : ToType (Φ.obj _)) (hf'.trans (map_zero _).symm)
  rw [map_zero] at ha
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom a)
  refine ⟨F, h, m, ?_⟩
  have e : a = homOfLE (n.le_add_right m) := rfl
  rw [← ha, e]
  change _ = Φ.map ((padicIntegersSheafMulSequence T l F.1).map _) _
  rw [padicIntegersSheafMulSequence_map_homOfLE, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

variable (T) in
/-- The maps `ℓ⁻ⁿ : 𝒪_{E,T} ⟶ ℚ̄_ℓ,T` are compatible with the inclusions `𝒪_{E,T} ⟶ 𝒪_{F,T}`. -/
lemma mapOfLE_comp_adicConstantSheafLeg {E F : FiniteIntermediateField l} (h : E.1 ≤ F.1)
    (n : ℕ) :
    (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (padicIntegersSheafMapOfLE T l h) ≫
      adicConstantSheafLeg T l F n = adicConstantSheafLeg T l E n := by
  rw [adicConstantSheafLeg, ← Category.assoc, ← padicSubfieldSheafCocone_ι_comp_mapOfLE,
    Category.assoc, adicConstantSheafLeg]
  congr 1
  exact ((padicAlgClSheafCocone T l).extend
    (padicAlgClSheafIsoAdicConstantSheaf T l).hom).w (homOfLE h : E ⟶ F)

/-- `AlgebraicGeometry.ProEtale.exists_sections_adicConstantSheafLeg_eq` with `E` containing a
given finite extension `E₀`. -/
theorem exists_sections_adicConstantSheafLeg_eq_of_le (E₀ : FiniteIntermediateField l)
    (s : (upperStarRightDerivedSections g p i W).obj
      ((sheafCompose (ProEt.topology T) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).obj
        (adicConstantSheaf l T))) :
    ∃ (E : FiniteIntermediateField l) (_ : E₀.1 ≤ E.1) (n : ℕ)
      (y : (upperStarRightDerivedSections g p i W).obj
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (padicIntegersSheaf T l E.1))),
      (upperStarRightDerivedSections g p i W).map (adicConstantSheafLeg T l E n) y = s := by
  obtain ⟨E, n, y, rfl⟩ := exists_sections_adicConstantSheafLeg_eq g p i W l s
  let F : FiniteIntermediateField l := ⟨E.1 ⊔ E₀.1, inferInstance⟩
  have h : E.1 ≤ F.1 := le_sup_left
  refine ⟨F, le_sup_right, n, (upperStarRightDerivedSections g p i W).map
    ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (padicIntegersSheafMapOfLE T l h)) y, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, mapOfLE_comp_adicConstantSheafLeg]

end AlgebraicGeometry.ProEtale
