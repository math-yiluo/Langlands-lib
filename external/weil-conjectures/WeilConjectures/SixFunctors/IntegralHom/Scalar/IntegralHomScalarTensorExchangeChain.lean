/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralHomTensorSwap
/-! # Scalar compatibility of the signed chain interchange
Source: Stacks Tags 06YY and 0FPQ.
(blueprint: lem-sfb-integral-hom-scalar-tensor-exchange-chain)
-/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe d u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom
private theorem total_component_ext
    (X : AlgebraicGeometry.Scheme.{u})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (Modules.{u, u} X R) ℤ) (k : ℤ) (H : Modules.{u, u} X R)
    {f g : (((totalTensor.{u, u} X R).obj P).obj Q).X k ⟶ H}
    (h : ∀ (i j : ℤ) (hij : i + j = k) (U : (AlgebraicGeometry.Scheme.ProEt X)ᵒᵖ)
      (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
      f.val.app U (coefficientTensorGenerator.{u, u + 1, u}
        (AlgebraicGeometry.Scheme.ProEt.topology X) R P Q i j k hij U x y) =
      g.val.app U (coefficientTensorGenerator.{u, u + 1, u}
        (AlgebraicGeometry.Scheme.ProEt.topology X) R P Q i j k hij U x y)) : f = g := by
  letI := tensorLocalization.{u, u} X R
  letI := countableColimits.{u, u} X R
  letI := ordinaryTensorZero.{u, u} X R
  letI := ordinaryTensorObjZero.{u, u} X R
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1} (R := R)
    (P.X i) (Q.X j)).inv).mp
  apply (adj.homEquiv _ H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h i j hij U x y

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ)

private theorem unit_eq (b : IntegralHomReductionTensorData D l hl E X n)
    (M : completedIntegralModuleSheaves l E X D hl) :
    reductionUnit l E X D hl n M = b.scalarUnit.app M := by
  apply SheafOfModules.hom_ext
  ext U x
  erw [b.scalarUnit_normalize]
  exact (Classical.choose_spec (scalarReductionExtension_adjunction l E X n)) M U x

-- Compare sheafified total generators without unfolding the derived constructions.
/-- The normalized ordinary comparison commutes with Koszul interchange.
Source: Stacks 06YY and 0FPQ. Proof: cancel the invertible ordinary comparison
and transpose each component through ordinary scalar extension. Pure total-tensor
generators suffice by sheafification and totalization. Naturality of the scalar
unit and the two normalized formulas give the same Koszul-signed generator.
(blueprint: lem-sfb-integral-hom-scalar-tensor-exchange-chain) -/
theorem scalarTensorExchange_chain
    (b : IntegralHomReductionTensorData D l hl E X n)
    (P Q : CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ)
    (β : ((totalTensor.{u, u} X (integralCoefficientCommRingSheaf l E X n)).obj
        (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj P)).obj
        (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj Q) ≅
      ((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj
        (((totalTensor.{u, u} X (completedIntegralCommRingSheaf l E X D hl)).obj P).obj Q))
    (hβ : ∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt X)ᵒᵖ)
      (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
      (β.hom.f (i + j)).val.app U
        (totalPair.{u, u} X (integralCoefficientCommRingSheaf l E X n)
          (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj P)
          (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj Q)
          i j U ((reductionUnit l E X D hl n (P.X i)).val.app U x)
            ((reductionUnit l E X D hl n (Q.X j)).val.app U y)) =
        (reductionUnit l E X D hl n
          ((((totalTensor.{u, u} X (completedIntegralCommRingSheaf l E X D hl)).obj P).obj Q).X
            (i + j))).val.app U
          (totalPair.{u, u} X (completedIntegralCommRingSheaf l E X D hl) P Q i j U x y)) :
    β.hom ≫
        ((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).map
          (tensorRepresentativeSwap (completedIntegralCommRingSheaf l E X D hl) P Q).hom ≫
        b.total Q P =
      (tensorRepresentativeSwap (integralCoefficientCommRingSheaf l E X n)
        (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)).obj P)
        (((integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex
          (.up ℤ)).obj Q)).hom := by
  classical
  let F := (integralReductionChangeOfRings l E X D hl n).mapHomologicalComplex (.up ℤ)
  let R := completedIntegralCommRingSheaf l E X D hl
  let S := integralCoefficientCommRingSheaf l E X n
  let σ := (tensorRepresentativeSwap R P Q).hom
  let τ := (tensorRepresentativeSwap S (F.obj P) (F.obj Q)).hom
  suffices he : F.map σ ≫ b.total Q P = β.inv ≫ τ by
    change β.hom ≫ F.map σ ≫ b.total Q P = τ
    rw [he, Iso.hom_inv_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext k
  let adj := Classical.choose (scalarReductionExtension_adjunction l E X n)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply total_component_ext X R P Q k
  intro i j hij U x y
  subst k
  have hu := unit_eq D l hl E X n b
  have hv := hβ i j U x y
  simp only [hu] at hv
  let z := totalPair.{u, u} X S (F.obj P) (F.obj Q) i j U
    ((b.scalarUnit.app (P.X i)).val.app U x) ((b.scalarUnit.app (Q.X j)).val.app U y)
  have hinv : (β.inv.f (i + j)).val.app U
      ((b.scalarUnit.app
        ((((totalTensor.{u, u} X R).obj P).obj Q).X (i + j))).val.app U
        (totalPair.{u, u} X R P Q i j U x y)) = z := by
    erw [← hv]
    have h := congrArg (fun f ↦ (f.f (i + j)).val.app U z) β.hom_inv_id
    change (β.inv.f (i + j)).val.app U ((β.hom.f (i + j)).val.app U z) = z at h
    exact h
  change ((b.total Q P).f (i + j)).val.app U
      (((F.map σ).f (i + j)).val.app U
        ((reductionUnit l E X D hl n _).val.app U
          (totalPair.{u, u} X R P Q i j U x y))) =
    (τ.f (i + j)).val.app U ((β.inv.f (i + j)).val.app U
      ((reductionUnit l E X D hl n _).val.app U
        (totalPair.{u, u} X R P Q i j U x y)))
  erw [hu, hinv]
  have hn := congrArg (fun f ↦ f.val.app U (totalPair.{u, u} X R P Q i j U x y))
    (b.scalarUnit.naturality (σ.f (i + j)))
  change (b.scalarUnit.app _).val.app U ((σ.f (i + j)).val.app U
      (totalPair.{u, u} X R P Q i j U x y)) =
    ((F.map σ).f (i + j)).val.app U ((b.scalarUnit.app _).val.app U
      (totalPair.{u, u} X R P Q i j U x y)) at hn
  erw [← hn]
  have hs := tensorRepresentativeSwap_pure R P Q i j (i + j) rfl (add_comm j i) U x y
  have ht := tensorRepresentativeSwap_pure S (F.obj P) (F.obj Q) i j (i + j) rfl
    (add_comm j i) U ((b.scalarUnit.app (P.X i)).val.app U x)
      ((b.scalarUnit.app (Q.X j)).val.app U y)
  change (σ.f (i + j)).val.app U (totalPair.{u, u} X R P Q i j U x y) = _ at hs
  erw [hs]
  simp only [Units.smul_def, map_zsmul]
  have htotal : ∀ (k : ℤ) (hji : j + i = k),
      ((b.total Q P).f k).val.app U
        ((b.scalarUnit.app ((homReductionTotal R Q P).X k)).val.app U
          (coefficientTensorGenerator.{u, u + 1, u}
            (AlgebraicGeometry.Scheme.ProEt.topology X) R Q P j i k hji U y x)) =
      coefficientTensorGenerator.{u, u + 1, u}
        (AlgebraicGeometry.Scheme.ProEt.topology X) S (F.obj Q) (F.obj P) j i k hji U
        ((b.scalarUnit.app (Q.X j)).val.app U y)
        ((b.scalarUnit.app (P.X i)).val.app U x) := by
    intro k hji
    subst k
    exact b.total_normalize Q P j i U y x
  erw [htotal (i + j) (add_comm j i)]
  exact ht.symm
end WeilConjectures.IntegralHom
