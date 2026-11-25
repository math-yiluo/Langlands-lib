/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat

/-!

# `F_X` is free over `E_X`

Let `ℓ` be a prime, `E ≤ F` finite subextensions of `ℚ̄_ℓ` over `ℚ_ℓ` and `X` a scheme. This file
proves that `F_X = p_X^* F̲` is a free module of rank `[F : E]` over `E_X = p_X^* E̲`: for an
`E`-basis `e₁, …, eₙ` of `F` (`PadicAlgCl.FiniteIntermediateField.basisOfLE`), the global
sections `eᵢ` of `F_X` (`AlgebraicGeometry.ProEtale.padicSubfieldBasisSection`) induce an
isomorphism `E_X^{⊕ n} ⟶ F_X`, `(aᵢ) ↦ ∑ aᵢ eᵢ`
(`AlgebraicGeometry.ProEtale.isIso_biproductDesc_padicSubfieldBasisSection`).

The proof proceeds in three steps.

* On condensed abelian groups, multiplying with the global section `η ≫ t` of a condensed ring
  `T̲ = C(-, T)` defined by a constant `t : T` is the multiplication by the constant `t`
  (`Profinite.leftUnitor_inv_comp_whiskerRight_comp_mul_eq_continuousMapRingObjMulLeft`). This
  is checked on presheaves through the lax monoidal structure of `sheafToPresheaf`.
* On condensed abelian groups, `⊞ᵢ E̲ ⟶ F̲`, `(fᵢ) ↦ ∑ eᵢ fᵢ`, is an isomorphism
  (`Profinite.isIso_biproductDesc_padicSubfieldRingObjMap_comp_mulLeft`), with inverse given by
  the coordinate functions of the basis, which are continuous: they are `ℚ_ℓ`-linear maps out of
  the finite dimensional normed `ℚ_ℓ`-space `F`.
* The strong monoidal additive functor `p_X^*` carries these statements to `X_proét`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ}

/-- For finite subextensions `E ≤ F`, the field `F` as an `E`-algebra through the inclusion
`E ⊆ F`. -/
noncomputable abbrev FiniteIntermediateField.algebraOfLE (h : E ≤ F) : Algebra E.1 F.1 :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

/-- The scalar towers `ℚ_ℓ ⊆ E ⊆ F`. -/
lemma FiniteIntermediateField.isScalarTower_algebraOfLE (h : E ≤ F) :
    letI := FiniteIntermediateField.algebraOfLE h
    IsScalarTower ℚ_[ℓ] E.1 F.1 :=
  letI := FiniteIntermediateField.algebraOfLE h
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- For finite subextensions `E ≤ F`, the field `F` is finite dimensional over `E`. -/
lemma FiniteIntermediateField.finiteDimensional_algebraOfLE (h : E ≤ F) :
    letI := FiniteIntermediateField.algebraOfLE h
    FiniteDimensional E.1 F.1 :=
  letI := FiniteIntermediateField.algebraOfLE h
  haveI := FiniteIntermediateField.isScalarTower_algebraOfLE h
  FiniteDimensional.right ℚ_[ℓ] E.1 F.1

/-- The degree `[F : E]` of finite subextensions `E ≤ F`. -/
noncomputable abbrev FiniteIntermediateField.finrankOfLE (h : E ≤ F) : ℕ :=
  letI := FiniteIntermediateField.algebraOfLE h
  Module.finrank E.1 F.1

/-- An `E`-basis of `F`, for finite subextensions `E ≤ F`, indexed by `Fin [F : E]`. -/
noncomputable def FiniteIntermediateField.basisOfLE (h : E ≤ F) :
    letI := FiniteIntermediateField.algebraOfLE h
    Module.Basis (Fin (FiniteIntermediateField.finrankOfLE h)) E.1 F.1 :=
  letI := FiniteIntermediateField.algebraOfLE h
  haveI := FiniteIntermediateField.finiteDimensional_algebraOfLE h
  Module.finBasis E.1 F.1

/-- The `i`-th coordinate function `F → E` of the basis `basisOfLE h`, as an additive map. -/
noncomputable def FiniteIntermediateField.basisOfLECoord (h : E ≤ F)
    (i : Fin (FiniteIntermediateField.finrankOfLE h)) : F.1 →+ E.1 :=
  letI := FiniteIntermediateField.algebraOfLE h
  ((LinearMap.proj i).comp
    (FiniteIntermediateField.basisOfLE h).equivFun.toLinearMap).toAddMonoidHom

/-- The coordinate functions of the basis `basisOfLE h` are continuous: they are `ℚ_ℓ`-linear
maps out of the finite dimensional normed `ℚ_ℓ`-space `F`. -/
lemma FiniteIntermediateField.continuous_basisOfLECoord (h : E ≤ F)
    (i : Fin (FiniteIntermediateField.finrankOfLE h)) :
    Continuous (FiniteIntermediateField.basisOfLECoord h i) := by
  let := FiniteIntermediateField.algebraOfLE h
  have := FiniteIntermediateField.isScalarTower_algebraOfLE h
  exact LinearMap.continuous_of_finiteDimensional
    (((LinearMap.proj i).comp
      (FiniteIntermediateField.basisOfLE h).equivFun.toLinearMap).restrictScalars ℚ_[ℓ])

/-- The `j`-th coordinate of `eᵢ x`, for the basis `eᵢ` of `F` over `E` and `x ∈ E`, is `δᵢⱼ x`. -/
lemma FiniteIntermediateField.basisOfLECoord_basisOfLE_mul (h : E ≤ F)
    (i j : Fin (FiniteIntermediateField.finrankOfLE h)) (x : E.1) :
    FiniteIntermediateField.basisOfLECoord h j
        ((letI := FiniteIntermediateField.algebraOfLE h
          FiniteIntermediateField.basisOfLE h i) * IntermediateField.inclusion h x) =
      if i = j then x else 0 := by
  let := FiniteIntermediateField.algebraOfLE h
  have hx : FiniteIntermediateField.basisOfLE h i * IntermediateField.inclusion h x =
      x • FiniteIntermediateField.basisOfLE h i := by
    rw [Algebra.smul_def, mul_comm]
    rfl
  rw [hx]
  simp [FiniteIntermediateField.basisOfLECoord, Module.Basis.equivFun_self]

/-- Every `y ∈ F` is `∑ⱼ eⱼ yⱼ`, for the basis `eⱼ` of `F` over `E` and the coordinates `yⱼ ∈ E`
of `y`. -/
lemma FiniteIntermediateField.sum_basisOfLE_mul_basisOfLECoord (h : E ≤ F) (y : F.1) :
    ∑ j, (letI := FiniteIntermediateField.algebraOfLE h
        FiniteIntermediateField.basisOfLE h j) *
      IntermediateField.inclusion h (FiniteIntermediateField.basisOfLECoord h j y) = y := by
  let := FiniteIntermediateField.algebraOfLE h
  refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
    ((FiniteIntermediateField.basisOfLE h).sum_equivFun y)
  rw [Algebra.smul_def, mul_comm]
  rfl

end PadicAlgCl

namespace Profinite

section MulLeft

variable {T : Type} [TopologicalSpace T] [Ring T] [IsTopologicalRing T]

/-- On presheaves, the multiplication by a constant `t` on `C(-, T)` commutes with the
multiplication of `C(-, T)`: `(t a) b = t (a b)`. -/
lemma continuousMapRingObjMulLeft_hom_whiskerRight_comp_mul (t : T) :
    (continuousMapRingObjMulLeft.{u} T t).hom ▷
        (continuousMapRingPresheaf T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) ≫
      μ[continuousMapRingPresheaf T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}] =
    μ[continuousMapRingPresheaf T ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}] ≫
      (continuousMapRingObjMulLeft.{u} T t).hom := by
  ext S : 2
  refine AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ ?_)
  exact ULift.ext (_root_.mul_assoc _ _ _)

/-- The multiplication by a constant `t` on the condensed abelian group `C(-, T)` commutes with
the multiplication of the condensed ring `C(-, T)`. -/
lemma continuousMapRingObjMulLeft_whiskerRight_comp_mul (t : T) :
    continuousMapRingObjMulLeft.{u} T t ▷ continuousMapRingObj T ≫ μ[continuousMapRingObj T] =
      μ[continuousMapRingObj T] ≫ continuousMapRingObjMulLeft T t := by
  refine Sheaf.hom_ext_of_μ_comp ?_
  have h := Sheaf.μ_sheafToPresheaf_comp_map_mul_sheafCompose (coherentTopology Profinite.{u})
    (continuousMapRingSheaf.{u} T)
  rw [Functor.map_comp, Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_left_assoc,
    reassoc_of% h, h]
  exact continuousMapRingObjMulLeft_hom_whiskerRight_comp_mul t

/-- Multiplication with the global section `η ≫ t` of the condensed ring `C(-, T)` defined by a
constant `t : T` is the multiplication by the constant `t`. -/
lemma leftUnitor_inv_comp_whiskerRight_comp_mul_eq_continuousMapRingObjMulLeft (t : T) :
    (λ_ (continuousMapRingObj.{u} T)).inv ≫
        (η[continuousMapRingObj T] ≫ continuousMapRingObjMulLeft T t) ▷ continuousMapRingObj T ≫
        μ[continuousMapRingObj T] =
      continuousMapRingObjMulLeft T t := by
  rw [comp_whiskerRight, Category.assoc, continuousMapRingObjMulLeft_whiskerRight_comp_mul,
    MonObj.one_mul_assoc, Iso.inv_hom_id_assoc]

variable {T' : Type} [TopologicalSpace T'] [Ring T'] [IsTopologicalRing T']

/-- Postcomposition with a continuous additive map `φ : T →+ T'`, as a morphism of condensed
abelian groups `C(-, T) ⟶ C(-, T')`. -/
noncomputable def continuousMapRingObjMapOfAddMonoidHom (φ : T →+ T') (hφ : Continuous φ) :
    continuousMapRingObj.{u} T ⟶ continuousMapRingObj T' :=
  ⟨{ app _ := AddCommGrpCat.ofHom
        { toFun a := ULift.up ((⟨φ, hφ⟩ : C(T, T')).comp a.down)
          map_zero' := ULift.ext (ContinuousMap.ext fun _ ↦ map_zero φ)
          map_add' _ _ := ULift.ext (ContinuousMap.ext fun _ ↦ map_add φ _ _) }
     naturality _ _ _ := rfl }⟩

/-- The sections of `continuousMapRingObjMapOfAddMonoidHom φ hφ` are given by postcomposition
with `φ`. -/
lemma continuousMapRingObjMapOfAddMonoidHom_app_apply (φ : T →+ T') (hφ : Continuous φ)
    (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} C(S.unop, T)) :
    (continuousMapRingObjMapOfAddMonoidHom φ hφ).hom.app S a =
      ULift.up ((⟨φ, hφ⟩ : C(T, T')).comp a.down) :=
  rfl

/-- A finite sum of morphisms of condensed abelian groups `C(-, T) ⟶ C(-, T')` is computed
pointwise on sections. -/
lemma sum_hom_app_apply_down {J : Type*} [Fintype J]
    (f : J → (continuousMapRingObj.{u} T ⟶ continuousMapRingObj T')) (S : Profinite.{u}ᵒᵖ)
    (a : ULift.{u + 1} C(S.unop, T)) (s : S.unop) :
    ((∑ j, f j).hom.app S a).down s = ∑ j, ((f j).hom.app S a).down s := by
  have h₁ : (∑ j, f j).hom.app S = ∑ j, (f j).hom.app S :=
    (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
      (evaluation _ _).obj S).map_sum f Finset.univ
  have h₂ : (∑ j, (f j).hom.app S) a = ∑ j, (f j).hom.app S a :=
    (congrArg (fun φ : _ →+ _ ↦ φ a)
      (map_sum AddCommGrpCat.homAddEquiv (fun j ↦ (f j).hom.app S) Finset.univ)).trans
      (AddMonoidHom.finsetSum_apply _ _ _)
  rw [h₁, h₂]
  exact (congrArg (fun g : C(S.unop, T') ↦ g s) (map_sum ULift.ringEquiv _ Finset.univ)).trans
    (ContinuousMap.sum_apply _ _ _)

end MulLeft

end Profinite

namespace Profinite

open _root_.PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ}

/-- **`F̲ ≅ E̲^{⊕ [F : E]}`**: for finite subextensions `E ≤ F` and the `E`-basis `eᵢ` of `F`,
the map `⊞ᵢ E̲ ⟶ F̲`, `(fᵢ) ↦ ∑ eᵢ fᵢ`, of condensed abelian groups is an isomorphism. Its
inverse is given by the (continuous) coordinate functions of the basis. -/
lemma isIso_biproductDesc_padicSubfieldRingObjMap_comp_mulLeft (h : E ≤ F) :
    IsIso (biproduct.desc fun i ↦ padicSubfieldRingObjMap.{u} ℓ h ≫
      continuousMapRingObjMulLeft F.1 (FiniteIntermediateField.basisOfLE h i)) := by
  let := FiniteIntermediateField.algebraOfLE h
  refine ⟨biproduct.lift fun i ↦ continuousMapRingObjMapOfAddMonoidHom
    (FiniteIntermediateField.basisOfLECoord h i)
    (FiniteIntermediateField.continuous_basisOfLECoord h i), ?_, ?_⟩
  · refine biproduct.hom_ext' _ _ fun i ↦ biproduct.hom_ext _ _ fun j ↦ ?_
    simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.comp_id]
    by_cases hij : i = j
    · subst hij
      rw [biproduct.ι_π_self]
      ext S a
      refine ULift.ext (ContinuousMap.ext fun s ↦ ?_)
      exact (FiniteIntermediateField.basisOfLECoord_basisOfLE_mul h i i (a.down s)).trans
        (ite_eq_left rfl)
    · rw [biproduct.ι_π_ne _ hij]
      ext S a
      refine ULift.ext (ContinuousMap.ext fun s ↦ ?_)
      exact (FiniteIntermediateField.basisOfLECoord_basisOfLE_mul h i j (a.down s)).trans
        (ite_eq_right hij)
  · rw [biproduct.lift_desc]
    ext S a
    refine ULift.ext (ContinuousMap.ext fun s ↦ ?_)
    rw [sum_hom_app_apply_down]
    exact FiniteIntermediateField.sum_basisOfLE_mul_basisOfLECoord h (a.down s)

end Profinite

namespace CategoryTheory.Functor.LaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (G : C ⥤ D) [G.LaxMonoidal]

/-- For a lax monoidal functor `G` and a monoid object `B`, multiplication on `G B` with the
global section `ε ≫ G s` is the image under `G` of the multiplication with the global section
`s` of `B`. -/
lemma leftUnitor_inv_comp_whiskerRight_comp_mul_obj {B : C} [MonObj B] (s : 𝟙_ C ⟶ B) :
    (λ_ (G.obj B)).inv ≫ (ε G ≫ G.map s) ▷ G.obj B ≫ μ[G.obj B] =
      G.map ((λ_ B).inv ≫ s ▷ B ≫ μ[B]) := by
  rw [Functor.obj.μ_def, comp_whiskerRight, Category.assoc,
    μ_natural_left_assoc, left_unitality_inv_assoc, Functor.map_comp, Functor.map_comp]

end CategoryTheory.Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl Functor.LaxMonoidal

variable (X : Scheme.{u}) {ℓ : ℕ} [Fact ℓ.Prime] {E F : FiniteIntermediateField ℓ}

/-- The global section `eᵢ` of `F_X`, for the basis `eᵢ` of `F` over `E`
(`PadicAlgCl.FiniteIntermediateField.basisOfLE`): the image under `p_X^*` of the global section
`η ≫ eᵢ` of the condensed ring `F̲`. -/
noncomputable def padicSubfieldBasisSection (h : E ≤ F)
    (i : Fin (FiniteIntermediateField.finrankOfLE h)) :
    𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1}) ⟶ padicSubfieldRingObj X ℓ F :=
  η[padicSubfieldRingObj X ℓ F] ≫ (upperStarFromPoint X).map
    (Profinite.continuousMapRingObjMulLeft F.1 (FiniteIntermediateField.basisOfLE h i))

/-- The global section `eᵢ` of `F_X` is `ε ≫ p_X^* (η ≫ eᵢ)`. -/
lemma padicSubfieldBasisSection_eq (h : E ≤ F)
    (i : Fin (FiniteIntermediateField.finrankOfLE h)) :
    padicSubfieldBasisSection X h i = ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map
      (η[Profinite.continuousMapRingObj F.1] ≫
        Profinite.continuousMapRingObjMulLeft F.1 (FiniteIntermediateField.basisOfLE h i)) := by
  rw [padicSubfieldBasisSection, Functor.map_comp, ← Category.assoc]
  rfl

/-- **`F_X` is free over `E_X`**: for finite subextensions `E ≤ F` and the basis `eᵢ` of `F` over
`E`, the map `E_X^{⊕ [F : E]} ⟶ F_X`, `(aᵢ) ↦ ∑ aᵢ eᵢ`, is an isomorphism. It is the image under
the additive strong monoidal functor `p_X^*` of the isomorphism `⊞ᵢ E̲ ⟶ F̲` of
`Profinite.isIso_biproductDesc_padicSubfieldRingObjMap_comp_mulLeft`. -/
theorem isIso_biproductDesc_padicSubfieldBasisSection (h : E ≤ F) :
    IsIso (biproduct.desc fun i ↦ padicSubfieldRingObjMap X ℓ h ≫
      (λ_ (padicSubfieldRingObj X ℓ F)).inv ≫ padicSubfieldBasisSection X h i ▷ _ ≫
      μ[padicSubfieldRingObj X ℓ F]) := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  have := Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)
  have := Profinite.isIso_biproductDesc_padicSubfieldRingObjMap_comp_mulLeft.{u} ℓ h
  have hi : (fun i ↦ padicSubfieldRingObjMap X ℓ h ≫
      (λ_ (padicSubfieldRingObj X ℓ F)).inv ≫ padicSubfieldBasisSection X h i ▷ _ ≫
      μ[padicSubfieldRingObj X ℓ F]) = fun i ↦ (upperStarFromPoint X).map
        (Profinite.padicSubfieldRingObjMap ℓ h ≫
          Profinite.continuousMapRingObjMulLeft F.1 (FiniteIntermediateField.basisOfLE h i)) := by
    refine funext fun i ↦ ?_
    rw [padicSubfieldBasisSection_eq, leftUnitor_inv_comp_whiskerRight_comp_mul_obj,
      Profinite.leftUnitor_inv_comp_whiskerRight_comp_mul_eq_continuousMapRingObjMulLeft,
      Functor.map_comp]
  rw [hi, ← biproduct.mapBiproduct_inv_map_desc]
  infer_instance

end AlgebraicGeometry.ProEtale
