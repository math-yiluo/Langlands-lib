/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.QuotPowExtension

/-!
# Uniform finite local constancy of the tower `Hᵏ(Rg_* (Λ ⧸ Iⁿ))` on a stratum

Let `Λ` be a noetherian ring, `I = (ϖ)` with `ϖ` a nonzerodivisor and all `Λ ⧸ Iⁿ` finite (the
case `Λ = 𝒪_E`, `ϖ = ℓ`), `g : T ⟶ Y` a morphism of schemes and `j : S ⟶ Y` a stratum over which
all the higher direct images `Rᵏg_* (Λ ⧸ I)_T` of sheaves of `Λ ⧸ I`-modules restrict to finite
locally constant sheaves. Then:

- `AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_upperStar_higherDirectImageQuotPowTower`:
  every level `j^* Hᵏ(Rg_* (Λ ⧸ Iⁿ))` of the restricted tower
  (`AlgebraicGeometry.Etale.higherDirectImageQuotPowTower`), for all `n : ℕ` and `k : ℤ`, is a
  finite locally constant sheaf of `Λ`-modules. This is the long exact sequence of the
  triangles attached to `0 ⟶ Λ ⧸ I ⟶ Λ ⧸ Iⁿ⁺¹ ⟶ Λ ⧸ Iⁿ ⟶ 0`, the extension property of finite
  locally constant sheaves killed by `Iⁿ⁺¹`
  (`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_shortExact_of_smul_eq_zero`) and
  the vanishing in negative degrees;
- `AlgebraicGeometry.Etale.isSetFLC_upperStar_higherDirectImageQuotPowTower_obj_of_flcProperty_one`:
  hence these levels are `IsSetFLC`, the hypothesis of the integral identification on a stratum
  (`AlgebraicGeometry.ProEtale.nonempty_iso_homologyUpperStar_integersStratum`);
- `AlgebraicGeometry.Etale.flcProperty_upperStar_rightDerived_constantQuotSheaf_pow`: and the
  `Rᵏg_* (Λ ⧸ Iⁿ)_T`, computed over `Λ ⧸ Iⁿ`, restrict to finite locally constant sheaves of
  `Λ ⧸ Iⁿ`-modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ) {T Y S : Scheme.{u}} (g : T ⟶ Y)
  (j : S ⟶ Y)

/-- The first level of the tower: `H^i(Rg_* (Λ ⧸ I¹)_T)`, computed in `D(T_ét, Λ)`, is the higher
direct image `Rⁱg_* (Λ ⧸ I)_T` of sheaves of `Λ ⧸ I`-modules with scalars restricted to `Λ`. -/
noncomputable def higherDirectImageQuotPowTowerObjOneIso (i : ℕ) :
    (higherDirectImageQuotPowTower I g i).obj (op 1) ≅
      (Sheaf.restrictScalars Y.smallEtaleTopology (Ideal.Quotient.mk I)).obj
        (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)].rightDerived i).obj (constantQuotSheaf Λ I T)) :=
  (_root_.DerivedCategory.homologyFunctor _ i).mapIso
      ((R((g)_*[ModuleCat.{u + 1} Λ])).mapIso ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
          (restrictScalarsConstantQuotSheafIso I T).symm) ≪≫
        (restrictScalarsRightDerivedLowerStarSingleIso (Ideal.Quotient.mk I) g _).symm) ≪≫
    (((Sheaf.restrictScalars Y.smallEtaleTopology
      (Ideal.Quotient.mk I)).mapDerivedCategoryHomologyFunctorIso i).app _).symm ≪≫
    (Sheaf.restrictScalars Y.smallEtaleTopology (Ideal.Quotient.mk I)).mapIso
      (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)]).homologyRightDerivedFunctorObjSingleFunctorIso _ i)

/-- The `n`-th level of the tower is killed by `Iⁿ`. -/
lemma smul_id_higherDirectImageQuotPowTower_obj (i : ℤ) (n : ℕ) {r : Λ} (hr : r ∈ I ^ n) :
    r • 𝟙 ((higherDirectImageQuotPowTower I g i).obj (op n)) = 0 := by
  have hM : r • 𝟙 (ModuleCat.of Λ (Λ ⧸ I ^ n)) = 0 := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul (Ideal.Quotient.mk _),
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hr
  have := congrArg (fun f ↦ (_root_.DerivedCategory.homologyFunctor _ i).map
    ((R((g)_*[ModuleCat.{u + 1} Λ])).map ((_root_.DerivedCategory.singleFunctor _ 0).map
      ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map f))))
    (hM : r • 𝟙 ((Ideal.quotPowFunctor I).obj (op n)) = 0)
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] at this
  exact this

/-- The restricted `n`-th level of the tower is killed by `Iⁿ`. -/
lemma smul_id_upperStar_higherDirectImageQuotPowTower_obj (i : ℤ) (n : ℕ) {r : Λ}
    (hr : r ∈ I ^ n) :
    r • 𝟙 ((j)^*[ModuleCat.{u + 1} Λ].obj ((higherDirectImageQuotPowTower I g i).obj (op n))) =
      0 := by
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul,
    smul_id_higherDirectImageQuotPowTower_obj I g i n hr, Functor.map_zero]

/-- The tower vanishes in negative degrees. -/
lemma isZero_higherDirectImageQuotPowTower_obj {i : ℤ} (hi : i < 0) (n : ℕ) :
    IsZero ((higherDirectImageQuotPowTower I g i).obj (op n)) :=
  have := ((g)_*[ModuleCat.{u + 1} Λ]).isGE_rightDerivedFunctor_obj_singleFunctor
    ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      ((Ideal.quotPowFunctor I).obj (op n)))
  _root_.DerivedCategory.isZero_of_isGE _ 0 i hi

/-- The level `0` of the tower vanishes, `Λ ⧸ I⁰` being zero. -/
lemma isZero_upperStar_higherDirectImageQuotPowTower_obj_zero (i : ℤ) :
    IsZero ((j)^*[ModuleCat.{u + 1} Λ].obj ((higherDirectImageQuotPowTower I g i).obj (op 0))) := by
  rw [IsZero.iff_id_eq_zero, ← one_smul Λ (𝟙 _)]
  exact smul_id_upperStar_higherDirectImageQuotPowTower_obj I g j i 0 (by simp)

variable (Λ) in
/-- Finite local constancy, as a property of étale sheaves of modules over an arbitrary ring. -/
abbrev flcModuleProperty (X : Scheme.{u}) :
    ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fun F ↦ IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F

variable {I} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (hI : I = Ideal.span {ϖ})
include hϖ hI

/-- **Uniform finite local constancy of the tower on a stratum.** Let `Λ` be noetherian,
`I = (ϖ)` with `ϖ` a nonzerodivisor and all `Λ ⧸ Iⁿ` finite. If over `j : S ⟶ Y` all the higher
direct images `Rᵏg_* (Λ ⧸ I)_T` of sheaves of `Λ ⧸ I`-modules restrict to finite locally constant
sheaves, then so do all the levels `Hᵏ(Rg_* (Λ ⧸ Iⁿ)_T)` of the tower, as sheaves of
`Λ`-modules. -/
theorem isFiniteLocallyConstantSheaf_upperStar_higherDirectImageQuotPowTower
    [IsNoetherianRing Λ] [∀ n, Finite (Λ ⧸ I ^ n)] [Finite (Λ ⧸ I)]
    (h : ∀ k : ℕ, flcProperty S ((j)^*[ModuleCat.{u + 1} (Λ ⧸ I)].obj
      (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)].rightDerived k).obj (constantQuotSheaf Λ I T))))
    (n : ℕ) (k : ℤ) :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
      ((j)^*[ModuleCat.{u + 1} Λ].obj ((higherDirectImageQuotPowTower I g k).obj (op n))) := by
  let H : ℤ → ℕ → Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun k n ↦
    (j)^*[ModuleCat.{u + 1} Λ].obj ((higherDirectImageQuotPowTower I g k).obj (op n))
  change flcModuleProperty Λ S (H k n)
  have hbase (k : ℤ) : flcModuleProperty Λ S (H k 1) := by
    rcases lt_or_ge k 0 with hk | hk
    · exact IsFiniteLocallyConstantSheaf.of_isZero
        (Functor.map_isZero _ (isZero_higherDirectImageQuotPowTower_obj I g hk 1))
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      have := h k
      have : IsFiniteLocallyConstantSheaf (((j)^*[ModuleCat.{u + 1} (Λ ⧸ I)] ⋙
          Sheaf.restrictScalars S.smallEtaleTopology (Ideal.Quotient.mk I)).obj
            (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)].rightDerived k).obj
              (constantQuotSheaf Λ I T))) :=
        IsFiniteLocallyConstantSheaf.restrictScalars I _
      exact IsFiniteLocallyConstantSheaf.of_iso
        (((upperStarRestrictScalarsIso (Ideal.Quotient.mk I) j).app _).symm ≪≫
          (j)^*[ModuleCat.{u + 1} Λ].mapIso (higherDirectImageQuotPowTowerObjOneIso I g k).symm)
  have hker {X Z : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : X ⟶ Z)
      (hX : flcModuleProperty Λ S X) (hZ : flcModuleProperty Λ S Z) :
      flcModuleProperty Λ S (kernel φ) := by
    have := hX; have := hZ
    exact IsFiniteLocallyConstantSheaf.kernel φ
  have hcoker {X Z : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : X ⟶ Z)
      (hX : flcModuleProperty Λ S X) (hZ : flcModuleProperty Λ S Z) :
      flcModuleProperty Λ S (cokernel φ) := by
    have := hX; have := hZ
    exact IsFiniteLocallyConstantSheaf.cokernel φ
  have hsucc : ∀ (n : ℕ) (k : ℤ), flcModuleProperty Λ S (H k (n + 1)) := by
    intro n
    induction n with
    | zero => exact hbase
    | succ n ih =>
      intro k
      let SC := (DerivedCategory.quotPowSuccShortComplex I ϖ
        (DerivedCategory.mem_of_eq_span hI) (n + 1)).map
          (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      have hSC : SC.ShortExact :=
        (DerivedCategory.quotPowSuccShortComplex_shortExact hϖ hI (n + 1)).map_of_exact _
      let Tr := (R((g)_*[ModuleCat.{u + 1} Λ])).mapTriangle.obj hSC.singleTriangle
      have hTr : Tr ∈ distTriang _ :=
        (R((g)_*[ModuleCat.{u + 1} Λ])).map_distinguished _ hSC.singleTriangle_distinguished
      let F := (j)^*[ModuleCat.{u + 1} Λ]
      have hext {S' : ShortComplex (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
          (hS' : S'.ShortExact) (h₁ : flcModuleProperty Λ S S'.X₁)
          (h₃ : flcModuleProperty Λ S S'.X₃)
          (hQ : ∀ r ∈ I ^ (n + 2), r • 𝟙 S'.X₂ = 0) : flcModuleProperty Λ S S'.X₂ := by
        have := h₁; have := h₃
        exact IsFiniteLocallyConstantSheaf.of_shortExact_of_smul_eq_zero (I ^ (n + 2)) hS' hQ
      exact (flcModuleProperty Λ S).prop_of_exact_five_of_mid
        (fun X ↦ ∀ r ∈ I ^ (n + 2), r • 𝟙 X = 0) hker hcoker hext
        (F.map (_root_.DerivedCategory.HomologySequence.δ Tr (k - 1) k (by lia)))
        (F.map ((_root_.DerivedCategory.homologyFunctor _ k).map Tr.mor₁))
        (F.map ((_root_.DerivedCategory.homologyFunctor _ k).map Tr.mor₂))
        (F.map (_root_.DerivedCategory.HomologySequence.δ Tr k (k + 1) (by lia))) _ _ _
        ((_root_.DerivedCategory.HomologySequence.exact₁ Tr hTr (k - 1) k (by lia)).map F)
        ((_root_.DerivedCategory.HomologySequence.exact₂ Tr hTr k).map F)
        ((_root_.DerivedCategory.HomologySequence.exact₃ Tr hTr k (k + 1) (by lia)).map F)
        (ih (k - 1)) (hbase k) (ih k) (hbase (k + 1))
        (fun r hr ↦ smul_id_upperStar_higherDirectImageQuotPowTower_obj I g j k (n + 2) hr)
  cases n with
  | zero =>
    exact IsFiniteLocallyConstantSheaf.of_isZero
      (isZero_upperStar_higherDirectImageQuotPowTower_obj_zero I g j k)
  | succ n => exact hsucc n k

/-- **The restricted tower is `IsSetFLC`**, from the finite local constancy of the
`Rᵏg_* (Λ ⧸ I)_T` over the stratum: the hypothesis of the integral identification
`AlgebraicGeometry.ProEtale.nonempty_iso_homologyUpperStar_integersStratum`, in all degrees
`k : ℤ`. -/
theorem isSetFLC_upperStar_higherDirectImageQuotPowTower_obj_of_flcProperty_one
    [IsNoetherianRing Λ] [∀ n, Finite (Λ ⧸ I ^ n)] [Finite (Λ ⧸ I)]
    (h : ∀ k : ℕ, flcProperty S ((j)^*[ModuleCat.{u + 1} (Λ ⧸ I)].obj
      (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)].rightDerived k).obj (constantQuotSheaf Λ I T))))
    (n : ℕ) (k : ℤ) :
    IsSetFLC ((j)^*[ModuleCat.{u + 1} Λ].obj
      ((higherDirectImageQuotPowTower I g k).obj (op n))) := by
  have := isFiniteLocallyConstantSheaf_upperStar_higherDirectImageQuotPowTower g j hϖ hI h n k
  let e := Sheaf.restrictScalarsCoextendScalarsIso (J := I ^ n) _
    (fun r hr ↦ smul_id_upperStar_higherDirectImageQuotPowTower_obj I g j k n hr)
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) ((Sheaf.restrictScalars _
        (Ideal.Quotient.mk (I ^ n))).obj ((Sheaf.coextendScalars _ (I ^ n)).obj
          ((j)^*[ModuleCat.{u + 1} Λ].obj ((higherDirectImageQuotPowTower I g k).obj (op n))))) :=
    IsFiniteLocallyConstantSheaf.of_iso e.symm
  have := IsFiniteLocallyConstantSheaf.of_restrictScalars (I ^ n)
    ((Sheaf.coextendScalars _ (I ^ n)).obj
      ((j)^*[ModuleCat.{u + 1} Λ].obj ((higherDirectImageQuotPowTower I g k).obj (op n))))
  exact IsFiniteLocallyConstantSheafOfTypes.of_iso
    ((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).mapIso e)
    ((IsFiniteLocallyConstantSheaf.isSetFLC this).restrictScalars (Ideal.Quotient.mk (I ^ n)))

/-- **The `Rᵏg_* (Λ ⧸ Iⁿ)_T` are finite locally constant on the stratum**, as sheaves of
`Λ ⧸ Iⁿ`-modules, as soon as the `Rᵏg_* (Λ ⧸ I)_T` are. -/
theorem flcProperty_upperStar_rightDerived_constantQuotSheaf_pow
    [IsNoetherianRing Λ] [∀ n, Finite (Λ ⧸ I ^ n)] [Finite (Λ ⧸ I)]
    (h : ∀ k : ℕ, flcProperty S ((j)^*[ModuleCat.{u + 1} (Λ ⧸ I)].obj
      (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I)].rightDerived k).obj (constantQuotSheaf Λ I T))))
    (n k : ℕ) :
    flcProperty S ((j)^*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)].obj
      (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)].rightDerived k).obj
        (constantQuotSheaf Λ (I ^ n) T))) := by
  have := isFiniteLocallyConstantSheaf_upperStar_higherDirectImageQuotPowTower g j hϖ hI h n k
  have : IsFiniteLocallyConstantSheaf ((Sheaf.restrictScalars S.smallEtaleTopology
      (Ideal.Quotient.mk (I ^ n))).obj ((j)^*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)].obj
        (((g)_*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)].rightDerived k).obj
          (constantQuotSheaf Λ (I ^ n) T)))) :=
    IsFiniteLocallyConstantSheaf.of_iso
      ((j)^*[ModuleCat.{u + 1} Λ].mapIso (higherDirectImageQuotPowTowerObjIso I g k n) ≪≫
        (upperStarRestrictScalarsIso (Ideal.Quotient.mk (I ^ n)) j).app _)
  exact IsFiniteLocallyConstantSheaf.of_restrictScalars (I ^ n) _

end AlgebraicGeometry.Etale
