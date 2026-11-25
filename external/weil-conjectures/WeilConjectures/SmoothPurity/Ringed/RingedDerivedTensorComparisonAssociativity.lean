/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedTensorComparisonAssociativity
import WeilConjectures.SmoothPurity.Ringed.RingedTensorRepresentativeTransport

/-! # Derived associativity from coherent tensor representatives
Source: Stacks 0FPT, 06YU and 07A4.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.RingedForgetTensorTransposition
namespace WeilConjectures
attribute [local implicit_reducible] CoefficientClosedStructure.tensor
  coefficientTotalTensor coefficientKFlatInclusion
attribute [local irreducible] SheafOfModules.monoidalCategory coefficientTensorGenerator
  CoefficientTensorModels.iso DerivedCategory.Q

section RingedModels
universe c v r d c' v' r' d'
variable {V : Type c} [Category.{v} V] (J : GrothendieckTopology V)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{d} (RingedTensorModules.{c, v, r} J R)]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, d} J R))
  (T : CoefficientTensorModels.{r, c, v, d} J R S)
variable {V' : Type c'} [Category.{v'} V'] (J' : GrothendieckTopology V')
  [HasSheafify J' AddCommGrpCat.{max c' v' r'}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max c' v' r'}]
  (R' : Sheaf J' CommRingCat.{max c' v' r'})
  [HasDerivedCategory.{d'} (RingedTensorModules.{c', v', r'} J' R')]
  (SU : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c', v', r', d'} J' R'))
  (TU : CoefficientTensorModels.{r', c', v', d'} J' R' SU)

-- The model comparison uses four nested representative squares.
/-- Four normalized binary squares and chain coherence imply derived associativity.
Source: Stacks 0FPT, 06YU and 07A4
(blueprint: lem-pur-ringed-derived-tensor-comparison-associativity).
Proof: form the two source and two target nested total models. The chosen tensor
coherences supply pure-triple associators and their derived conjugation equations.
Replace their one-K-flat comparisons by the simultaneous tensor-model comparisons.
The four binary squares, model naturality, and chain associativity are precisely
the hypotheses of the generic representative pasting argument. That argument
cancels the nested model isomorphisms and gives the derived associativity equation.
Only the five displayed pullback K-flat assertions are needed. -/
theorem ringedDerivedTensorComparison_associativity
    (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{c', v', r'} J' R')
    [U.Additive]
    (rD : DerivedCategory (RingedTensorModules.{c, v, r} J R) ⥤
      DerivedCategory (RingedTensorModules.{c', v', r'} J' R'))
    (α : DerivedCategory.Q ⋙ rD ≅ U.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ρ : ∀ M N, rD.obj (S.tensor.obj (M, N)) ≅ SU.tensor.obj (rD.obj M, rD.obj N))
    (hρ : ∀ M N M' N' f g,
      rD.map (S.tensor.map (X := (M, N)) (Y := (M', N')) (f, g)) ≫ (ρ M' N').hom =
        (ρ M N).hom ≫ SU.tensor.map (rD.map f, rD.map g))
    (θ : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{r', c', v'} J' R')
    (hc : RingedTensorComparisonCoherence.{c, v, r, c', v', r'} J R J' R' U θ)
    {β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
      _ S.monoidal}
    {βU : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c', v', r'} J' R'))
      _ SU.monoidal}
    (K : RingedDerivedTensorCoherence.{c, v, r, d} J R S T β)
    (KU : RingedDerivedTensorCoherence.{c', v', r', d'} J' R' SU TU βU)
    (hbin : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (R := R) Q)
      (hFP : CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P))
      (hFQ : CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj Q)),
      rD.map (T.iso J R S P Q hP hQ).hom ≫
        (ρ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        SU.tensor.map
          (X := (rD.obj (DerivedCategory.Q.obj P), rD.obj (DerivedCategory.Q.obj Q)))
          (Y := (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj P),
            DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj Q)))
          (α.hom.app P, α.hom.app Q) =
      α.hom.app ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map (θ.hom.app (P, Q)) ≫
        (TU.iso J' R' SU ((U.mapHomologicalComplex (.up ℤ)).obj P)
          ((U.mapHomologicalComplex (.up ℤ)).obj Q) hFP hFQ).hom)
    (A B C : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients (R := R) A)
    (hB : CochainComplex.IsKFlatIndependentCoefficients (R := R) B)
    (hC : CochainComplex.IsKFlatIndependentCoefficients (R := R) C)
    (hFA : CochainComplex.IsKFlatIndependentCoefficients (R := R')
      ((U.mapHomologicalComplex (.up ℤ)).obj A))
    (hFB : CochainComplex.IsKFlatIndependentCoefficients (R := R')
      ((U.mapHomologicalComplex (.up ℤ)).obj B))
    (hFC : CochainComplex.IsKFlatIndependentCoefficients (R := R')
      ((U.mapHomologicalComplex (.up ℤ)).obj C))
    (hFAB : CochainComplex.IsKFlatIndependentCoefficients (R := R')
      ((U.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (A, B))))
    (hFBC : CochainComplex.IsKFlatIndependentCoefficients (R := R')
      ((U.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (B, C)))) :
    let M := DerivedCategory.Q.obj A
    let N := DerivedCategory.Q.obj B
    let P := DerivedCategory.Q.obj C
    rD.map (S.monoidal.associator M N P).hom ≫
      (ρ M (S.tensor.obj (N, P))).hom ≫
      SU.tensor.map
        (X := (rD.obj M, rD.obj (S.tensor.obj (N, P))))
        (Y := (rD.obj M, SU.tensor.obj (rD.obj N, rD.obj P)))
        (𝟙 (rD.obj M), (ρ N P).hom) =
    (ρ (S.tensor.obj (M, N)) P).hom ≫
      SU.tensor.map
        (X := (rD.obj (S.tensor.obj (M, N)), rD.obj P))
        (Y := (SU.tensor.obj (rD.obj M, rD.obj N), rD.obj P))
        ((ρ M N).hom, 𝟙 (rD.obj P)) ≫
      (SU.monoidal.associator (rD.obj M) (rD.obj N) (rD.obj P)).hom := by
  let F := U.mapHomologicalComplex (.up ℤ)
  let q := DerivedCategory.Q (C := RingedTensorModules.{c, v, r} J R)
  let qU := DerivedCategory.Q (C := RingedTensorModules.{c', v', r'} J' R')
  let t := coefficientTotalTensor.{r, c, v} J R
  let tU := coefficientTotalTensor.{r', c', v'} J' R'
  let δ := fun P Q ↦ θ.app (P, Q)
  have hAB := coefficientTotalTensor_isKFlat.{r, c, v} J R A B hA hB
  have hBC := coefficientTotalTensor_isKFlat.{r, c, v} J R B C hB hC
  have hUAB := coefficientTotalTensor_isKFlat.{r', c', v'}
    J' R' (F.obj A) (F.obj B) hFA hFB
  have hUBC := coefficientTotalTensor_isKFlat.{r', c', v'}
    J' R' (F.obj B) (F.obj C) hFB hFC
  let iAB := T.iso J R S A B hA hB
  let iBC := T.iso J R S B C hB hC
  let iL := T.iso J R S (t.obj (A, B)) C hAB hC
  let iR := T.iso J R S A (t.obj (B, C)) hA hBC
  let jAB := TU.iso J' R' SU (F.obj A) (F.obj B) hFA hFB
  let jBC := TU.iso J' R' SU (F.obj B) (F.obj C) hFB hFC
  let jL := TU.iso J' R' SU (tU.obj (F.obj A, F.obj B))
    (F.obj C) hUAB hFC
  let jR := TU.iso J' R' SU (F.obj A)
    (tU.obj (F.obj B, F.obj C)) hFA hUBC
  let jL₀ := TU.iso J' R' SU (F.obj (t.obj (A, B)))
    (F.obj C) hFAB hFC
  let jR₀ := TU.iso J' R' SU (F.obj A)
    (F.obj (t.obj (B, C))) hFA hFBC
  obtain ⟨a, ha, hea⟩ := coefficientTensorModel_associator_representative.{c, v, r, d}
    J R S T K A B C hA hB hC
  obtain ⟨aU, haU, heaU⟩ := coefficientTensorModel_associator_representative.{c', v', r', d'}
    J' R' SU TU KU (F.obj A) (F.obj B) (F.obj C) hFA hFB hFC
  apply coefficientRepresentativeTensorComparison_associativity (r := rD)
    S SU ρ hρ q qU F t tU α A B C
    (δ A B) (δ B C) (δ (t.obj (A, B)) C) (δ A (t.obj (B, C)))
    a aU
    iAB iBC iL iR jAB jBC jL jR jL₀ jR₀
  · have h := hbin A B hA hB hFA hFB
    dsimp only [δ, Iso.app_hom]
    exact h
  · have h := hbin B C hB hC hFB hFC
    dsimp only [δ, Iso.app_hom]
    exact h
  · have h := hbin (t.obj (A, B)) C hAB hC hFAB hFC
    dsimp only [δ, Iso.app_hom]
    exact h
  · have h := hbin A (t.obj (B, C)) hA hBC hFA hFBC
    dsimp only [δ, Iso.app_hom]
    exact h
  · exact hea
  · exact heaU
  · have h := coefficientTensorModel_iso_naturality_left.{c', v', r', d'}
      J' R' SU TU
      (F.obj (t.obj (A, B))) (tU.obj (F.obj A, F.obj B)) (F.obj C)
      hFAB hUAB hFC (δ A B).hom
    exact h
  · have h := coefficientTensorModel_iso_naturality_right.{c', v', r', d'}
      J' R' SU TU
      (F.obj A) (F.obj (t.obj (B, C))) (tU.obj (F.obj B, F.obj C))
      hFA hFBC hUBC (δ B C).hom
    exact h
  · have h := hc.model_associativity A B C a aU ha haU
    dsimp only [F, t, tU, δ, Iso.app_hom]
    exact h

end RingedModels
end WeilConjectures
