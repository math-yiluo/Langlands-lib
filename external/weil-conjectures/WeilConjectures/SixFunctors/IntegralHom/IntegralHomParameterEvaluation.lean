/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorKoszulExistence
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationCoefficient
import WeilConjectures.SixFunctors.IntegralHom.HomComplexTensorPureEquivalence
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomRepresentativeUncurry
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomParameterAdjunction
/-! Coherent evaluation for the integral tensor presentation.
Source: the representative evaluation step in the blueprint proof.
(blueprint: lem-sf-integral-hom-parameter-evaluation) -/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

open CategoryTheory.MonoidalCategory

section Transport

variable {A : Type*} [Category* A] {H : Aᵒᵖ × A ⥤ A}

/-- Swap a right tensor adjunction using the specified natural tensor exchange. -/
private noncomputable def swappedAdjunction
    (S : CoefficientClosedStructure H) (σ : S.tensor ≅ CategoryTheory.Prod.swap A A ⋙ S.tensor)
    (K : A) : (Functor.curry.obj S.tensor).obj K ⊣
      (Functor.curry.obj H).obj (op K) := by
  letI := S.monoidal
  exact (S.adjunction K).ofNatIsoLeft
    (NatIso.ofComponents (fun X ↦ (σ.app (K, X)).symm) (by
      intro X X' f
      have h := σ.inv.naturality (Prod.mkHom (𝟙 K) f)
      change (f ⊗ₘ 𝟙 K) ≫ σ.inv.app (K, X') = _ at h
      rw [tensorHom_id] at h
      exact h))

private noncomputable def swappedParameterAdjunction
    (S : CoefficientClosedStructure H) (σ : S.tensor ≅ CategoryTheory.Prod.swap A A ⋙ S.tensor) :
    Functor.curry.obj S.tensor ⊣₂ Functor.curry.obj H := by
  let := S.monoidal
  refine parameterAdjunctionOfCounit (swappedAdjunction S σ) ?_
  intro K K' W f
  change S.tensor.map (Prod.mkHom (𝟙 K) (H.map (Prod.mkHom f.op (𝟙 W)))) ≫
      σ.hom.app (K, H.obj (op K, W)) ≫ (S.adjunction K).counit.app W =
    S.tensor.map (Prod.mkHom f (𝟙 _)) ≫
      σ.hom.app (K', H.obj (op K', W)) ≫ (S.adjunction K').counit.app W
  rw [σ.hom.naturality_assoc, σ.hom.naturality_assoc]
  congr 1
  change (H.map (Prod.mkHom f.op (𝟙 W)) ⊗ₘ 𝟙 K) ≫ _ =
    (𝟙 (H.obj (op K', W)) ⊗ₘ f) ≫ _
  rw [tensorHom_id, id_tensorHom]
  exact S.evaluation_naturality K' K W f

private theorem swappedAdjunction_uncurry
    (S : CoefficientClosedStructure H) (σ : S.tensor ≅ CategoryTheory.Prod.swap A A ⋙ S.tensor)
    (K X I : A) (f : X ⟶ H.obj (op K, I)) :
    ((swappedAdjunction S σ K).homEquiv X I).symm f =
      σ.hom.app (K, X) ≫ (S.transpose X K I).symm f := by
  rw [swappedAdjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  rfl

private theorem curry_counit
    (F : A × A ⥤ A) (K : A) (adj : (Functor.curry.obj F).obj K ⊣
      (Functor.curry.obj H).obj (op K))
    (X I : A) (f : X ⟶ H.obj (op K, I)) :
    (adj.homEquiv X I).symm f =
      F.map (Prod.mkHom (𝟙 K) f) ≫ adj.counit.app I := by
  rw [Adjunction.homEquiv_symm_apply]
  rfl

private theorem map_comp_exchange {B : Type*} [Category* B] (F : A ⥤ B)
    {X Y Z : A} {W V : B} (a : W ⟶ F.obj X) (b : W ⟶ V)
    (c : V ⟶ F.obj Y) (d : V ⟶ F.obj Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : a ≫ F.map f = b ≫ c) (h' : c ≫ F.map g = d) :
    a ≫ F.map (f ≫ g) = b ≫ d := by
  rw [Functor.map_comp, ← Category.assoc, h, Category.assoc, h']

private theorem map_comp_swap_evaluation {B : Type*} [Category* B] (F : A ⥤ B)
    {P Q I : A} {X Y : B} (c : F.obj P ≅ X) (d : F.obj Q ≅ Y)
    (s : P ⟶ Q) (a : Q ⟶ I) (σ : X ⟶ Y) (e : Y ⟶ F.obj I)
    (hs : c.hom ≫ σ = F.map s ≫ d.hom) (ha : d.hom ≫ e = F.map a) :
    c.inv ≫ F.map (s ≫ a) = σ ≫ e := by
  rw [Functor.map_comp, ← ha, ← Category.assoc (F.map s), ← hs]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Transport

attribute [local irreducible] derivedInternalHomOfUniverses homComplexFunctor
  completedIntegralCommRingSheaf totalPair evaluate homModelMap

private theorem totalPair_eq_coefficientTensorGenerator
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    [EssentiallySmall.{t + 1} Y.ProEt]
    [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)}]
    [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)}]
    (P Q : CochainComplex (Modules.{t, u} Y R) ℤ) (i j : ℤ)
    (U : Y.ProEtᵒᵖ) (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    totalPair.{t, u} Y R P Q i j U x y = coefficientTensorGenerator.{u, t + 1, t}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R P Q i j (i + j) rfl U x y := by
  simp only [totalPair, pair, ordinaryTensor, coefficientTensorGenerator,
    CochainComplex.ιMapBifunctor, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rfl

private theorem tensor_presentation_parameter_evaluation_of_coefficients
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    [EssentiallySmall.{t + 1} Y.ProEt]
    [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)}]
    [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)}]
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses (AlgebraicGeometry.Scheme.ProEt.topology Y) R))
    (T : CoefficientTensorModels (AlgebraicGeometry.Scheme.ProEt.topology Y) R S)
    : ∃ adj : Functor.curry.obj S.tensor ⊣₂
        Functor.curry.obj (hom Y R),
    ∀ (P I S' : CochainComplex (Modules.{t, u} Y R) ℤ)
      (hP : flat.{t, u} Y R P)
      (hS : flat.{t, u} Y R S'), I.IsKInjective →
      ∀ q : S' ⟶ homComplex.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := R) P I,
      ∃ beta : ((totalTensor.{t, u} Y R).obj P).obj S' ⟶ I,
        (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
          (x : (P.X i).val.obj U) (s : (S'.X j).val.obj U),
          (beta.f (i + j)).val.app U
            (totalPair.{t, u} Y R P S' i j U x s) =
            (i * j).negOnePow • evaluate.{t, u} Y R P I j i U ((q.f j).val.app U s) x) ∧
        T.comparison.inv.app (⟨P, hP⟩, ⟨S', hS⟩) ≫ DerivedCategory.Q.map beta =
          S.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
            (DerivedCategory.Q.map q ≫ homModelMap.{t, u} Y R P I)) ≫
          (adj.adj (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I) := by
  let := derivedCategory.{t, u} Y R
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  have hkoszul := ringedTensor_koszul_exists.{t + 1, t, u, (max u (t + 1)) + 1} J R S T
  let σ := hkoszul.choose
  have hσ := hkoszul.choose_spec
  refine ⟨swappedParameterAdjunction S σ, ?_⟩
  intro P I S' hP hS _ q
  have hcomponent (K) :
      (swappedParameterAdjunction S σ).adj K = swappedAdjunction S σ K := by
    rfl
  simp only [hcomponent]
  have hrepresentative := hσ P S' hP hS
  let s := hrepresentative.choose
  have hs := hrepresentative.choose_spec.1
  have hsq := hrepresentative.choose_spec.2
  have huncurry := representative_uncurry_evaluation Y R S T S' P I hS hP q
  let ψ := huncurry.choose
  have hψ := huncurry.choose_spec.1
  have hu := huncurry.choose_spec.2
  refine ⟨s.hom ≫ ψ, ?_, ?_⟩
  · intro i j U x y
    change (ψ.f (i + j)).val.app U
      ((s.hom.f (i + j)).val.app U _) = _
    have hs' := hs i j (i + j) rfl (add_comm j i) U x y
    rw [totalPair_eq_coefficientTensorGenerator]
    rw [hs']
    simp only [Units.smul_def, map_zsmul]
    rw [hψ j i (i + j) (add_comm j i) rfl U y x]
    simp only [evaluate, projection, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
  · change (T.iso J R S P S' hP hS).inv ≫ DerivedCategory.Q.map (s.hom ≫ ψ) = _
    exact (map_comp_swap_evaluation DerivedCategory.Q
      (T.iso J R S P S' hP hS) (T.iso J R S S' P hS hP)
      s.hom ψ _ _ hsq hu).trans
      ((swappedAdjunction_uncurry S σ (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj S') (DerivedCategory.Q.obj I)
        (DerivedCategory.Q.map q ≫ homModelMap.{t, u} Y R P I)).symm.trans
          (curry_counit S.tensor (DerivedCategory.Q.obj P)
            (swappedAdjunction S σ (DerivedCategory.Q.obj P)) _ _ _))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
variable [EssentiallySmall.{t + 1} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]
-- The representative square elaborates independent site and coefficient universes.
/-- The signed representative evaluation uses an adjunction natural in its tensor parameter.

Source: Stacks Tags 08J9 and 06YU; the normalized Koszul exchange construction.
Proof: transport the native adjunction through the natural Koszul exchange. Its
counits are coherent by exchange naturality and the native evaluation law.
Uncurry the representative map and precompose with the signed chain exchange.
Its pure-section formula and localization square give the stated normalization.
(blueprint: lem-sf-integral-hom-parameter-evaluation) -/
theorem tensor_presentation_parameter_evaluation
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (completedIntegralCommRingSheaf l E Y D hl)))
    (T : CoefficientTensorModels (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheaf l E Y D hl) S)
    : ∃ adj : Functor.curry.obj S.tensor ⊣₂
        Functor.curry.obj (hom Y (completedIntegralCommRingSheaf l E Y D hl)),
    ∀ (P I S' : CochainComplex (Modules.{t,u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) ℤ)
      (hP : flat.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl) P)
      (hS : flat.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl) S'), I.IsKInjective →
      ∀ q : S' ⟶ homComplex.{t+1,t,max u (t+1),max u (t+1)}
        (R := completedIntegralCommRingSheaf l E Y D hl) P I,
      ∃ beta : ((totalTensor.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj S' ⟶ I,
        (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
          (x : (P.X i).val.obj U) (s : (S'.X j).val.obj U),
          (beta.f (i+j)).val.app U
            (totalPair.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl) P S' i j U x s) =
            (i*j).negOnePow • evaluate.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl)
              P I j i U ((q.f j).val.app U s) x) ∧
        T.comparison.inv.app (⟨P,hP⟩,⟨S',hS⟩) ≫ DerivedCategory.Q.map beta =
          S.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
            (DerivedCategory.Q.map q ≫ homModelMap.{t,u} Y
              (completedIntegralCommRingSheaf l E Y D hl) P I)) ≫
          (adj.adj (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I) := by
  exact tensor_presentation_parameter_evaluation_of_coefficients Y
    (completedIntegralCommRingSheaf l E Y D hl) S T
end WeilConjectures.IntegralHom
