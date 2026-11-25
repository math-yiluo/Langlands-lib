/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomRepresentativeUncurry

set_option linter.privateModule false

/-! # Signed evaluation for finite tensor presentations

The normalized left-tensor adjunction and its representative evaluation are
constructed together from the recorded Koszul symmetry.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
universe d t u a b
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.IntegralHom

private theorem swap_comparison {D : Type a} [Category.{b} D]
    {A B C D' F G I : D} (c : A ≅ B) (d : C ≅ D')
    (s : A ⟶ C) (b : B ⟶ D') (a : C ⟶ I)
    (f : B ⟶ F) (v : F ⟶ G) (g : D' ⟶ G) (ε : G ⟶ I)
    (hs : c.hom ≫ b = s ≫ d.hom) (hn : f ≫ v = b ≫ g)
    (hu : d.hom ≫ g ≫ ε = a) (ε' : F ⟶ I) (hε : ε' = v ≫ ε) :
    c.inv ≫ (s ≫ a) = f ≫ ε' := by
  rw [hε]
  apply (cancel_epi c.hom).1
  simp only [Iso.hom_inv_id_assoc]
  calc
    s ≫ a = s ≫ (d.hom ≫ g ≫ ε) := by rw [hu]
    _ = (s ≫ d.hom) ≫ g ≫ ε := by simp only [Category.assoc]
    _ = (c.hom ≫ b) ≫ g ≫ ε := by rw [hs]
    _ = c.hom ≫ (b ≫ g) ≫ ε := by simp only [Category.assoc]
    _ = c.hom ≫ (f ≫ v) ≫ ε := by rw [hn]
    _ = c.hom ≫ (f ≫ v ≫ ε) := by simp only [Category.assoc]

private theorem transpose_symm {D : Type a} [Category.{b} D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H) (X K Y : D)
    (f : X ⟶ H.obj (op K, Y)) :
    (S.transpose X K Y).symm f =
      S.tensor.map (Prod.mkHom f (𝟙 K)) ≫ (S.adjunction K).counit.app Y := by
  letI := S.monoidal
  change _ = (f ⊗ₘ 𝟙 K) ≫ _
  rw [MonoidalCategory.tensorHom_id]
  rfl

private theorem tensor_swap_naturality {D : Type a} [Category.{b} D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    (β : @SymmetricCategory D _ S.monoidal) (K X Y : D) (f : X ⟶ Y) :
    S.tensor.map (Prod.mkHom (𝟙 K) f) ≫
        (β.toBraidedCategory.braiding K Y).hom =
      (β.toBraidedCategory.braiding K X).hom ≫
        S.tensor.map (Prod.mkHom f (𝟙 K)) := by
  letI := S.monoidal
  letI := β
  exact BraidedCategory.braiding_naturality (𝟙 K) f

private theorem transported_evaluation {D : Type a} [Category.{b} D]
    {H : Dᵒᵖ × D ⥤ D} (S : CoefficientClosedStructure H)
    (β : @SymmetricCategory D _ S.monoidal) (K X M : D) {A C : D}
    (c : A ≅ S.tensor.obj (K, X)) (d : C ≅ S.tensor.obj (X, K))
    (s : A ⟶ C) (a : C ⟶ M) (f : X ⟶ H.obj (op K, M))
    (e : S.tensor.obj (K, H.obj (op K, M)) ⟶ M)
    (he : e = (β.toBraidedCategory.braiding K (H.obj (op K, M))).hom ≫
      (S.adjunction K).counit.app M)
    (hs : c.hom ≫ (β.toBraidedCategory.braiding K X).hom = s ≫ d.hom)
    (hu : d.hom ≫ (S.transpose X K M).symm f = a) :
    c.inv ≫ (s ≫ a) = S.tensor.map (Prod.mkHom (𝟙 K) f) ≫ e := by
  have hu' : d.hom ≫ S.tensor.map (Prod.mkHom f (𝟙 K)) ≫
      (S.adjunction K).counit.app M = a :=
    (congrArg (fun z ↦ d.hom ≫ z) (transpose_symm S X K M f)).symm.trans hu
  exact swap_comparison c d s (β.toBraidedCategory.braiding K X).hom a
    (S.tensor.map (Prod.mkHom (𝟙 K) f))
    (β.toBraidedCategory.braiding K (H.obj (op K, M))).hom
    (S.tensor.map (Prod.mkHom f (𝟙 K))) ((S.adjunction K).counit.app M)
    hs (tensor_swap_naturality S β K X (H.obj (op K, M)) f) hu' e he

section Representatives
variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
  [EssentiallySmall.{t + 1} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]

attribute [local irreducible] homModelMap homComplexFunctor derivedInternalHomOfUniverses

variable
  (S : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{t + 1, t, u, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R))
  (T : CoefficientTensorModels.{u, t + 1, t, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R S)

-- Keep the representative calculation separate from construction of the adjunction.
private theorem evaluation_for_adj
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{t + 1, t, u, (max u (t + 1)) + 1}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R))
    (T : CoefficientTensorModels.{u, t + 1, t, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R S)
    (β : @SymmetricCategory (DerivedCategory (Modules.{t, u} Y R)) _ S.monoidal)
    (adj : ∀ K : DerivedCategory (Modules.{t, u} Y R),
      (Functor.curry.obj S.tensor).obj K ⊣
        (Functor.curry.obj (derivedInternalHomOfUniverses.{t + 1, t, u,
          (max u (t + 1)) + 1} (AlgebraicGeometry.Scheme.ProEt.topology Y) R)).obj (op K))
    (hadj : ∀ K M, (adj K).counit.app M =
      (β.toBraidedCategory.braiding K
        ((derivedInternalHomOfUniverses.{t + 1, t, u, (max u (t + 1)) + 1}
          (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (op K, M))).hom ≫
        (S.adjunction K).counit.app M)
    (hβ : RingedDerivedTensorSymmetryModel.{t + 1, t, u, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R S T β) :
    ∀ (P I S' : CochainComplex (Modules.{t, u} Y R) ℤ)
      (hP : flat.{t, u} Y R P) (hS : flat.{t, u} Y R S'), I.IsKInjective →
      ∀ q : S' ⟶ homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I,
      ∃ beta : (coefficientTotalTensor.{u, t + 1, t}
          (AlgebraicGeometry.Scheme.ProEt.topology Y) R).obj (P, S') ⟶ I,
        (∀ i j U x s, (beta.f (i + j)).val.app U
          (coefficientTensorGenerator.{u, t + 1, t}
            (AlgebraicGeometry.Scheme.ProEt.topology Y) R P S' i j (i + j) rfl U x s) =
          (i * j).negOnePow •
            ((((q.f j ≫ homComplexπ P I j i (i + j) rfl).val.app U s).app
              (op (Over.mk (𝟙 U.unop)))) x)) ∧
        T.comparison.inv.app (⟨P, hP⟩, ⟨S', hS⟩) ≫ DerivedCategory.Q.map beta =
          S.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
            (DerivedCategory.Q.map q ≫ homModelMap.{t, u} Y R P I)) ≫
          (adj (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I) := by
  classical
  letI := S.monoidal
  letI := β
  intro P I S' hP hS hI q
  have hswap := hβ P S' hP hS
  let s := hswap.choose
  have hs := hswap.choose_spec.1
  have hsq := hswap.choose_spec.2
  have huncurry := representative_uncurry_evaluation Y R S T S' P I hS hP q
  let a := huncurry.choose
  have ha := huncurry.choose_spec.1
  have hu := huncurry.choose_spec.2
  refine ⟨s.hom ≫ a, ?_, ?_⟩
  · intro i j U x y
    change (a.f (i + j)).val.app U
      ((s.hom.f (i + j)).val.app U
        (coefficientTensorGenerator.{u, t + 1, t}
          (AlgebraicGeometry.Scheme.ProEt.topology Y) R P S' i j (i + j) rfl U x y)) = _
    rw [hs i j (i + j) rfl (by omega)]
    simp only [Units.smul_def, map_zsmul]
    rw [ha j i (i + j) (by omega) rfl U y x]
  · let c := T.comparison.app (⟨P, hP⟩, ⟨S', hS⟩)
    let d := T.comparison.app (⟨S', hS⟩, ⟨P, hP⟩)
    let ss := DerivedCategory.Q.map s.hom
    let aa := DerivedCategory.Q.map a
    let f := DerivedCategory.Q.map q ≫ homModelMap Y R P I
    let e := (adj (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I)
    have h := transported_evaluation (D := DerivedCategory (Modules.{t, u} Y R))
      (H := hom.{t, u} Y R) S β (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj S') (DerivedCategory.Q.obj I) c d ss aa f e
      (hadj (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)) hsq hu
    exact (congrArg
      (fun f ↦ T.comparison.inv.app (⟨P, hP⟩, ⟨S', hS⟩) ≫ f)
      (DerivedCategory.Q.map_comp s.hom a)).trans h

end Representatives
end WeilConjectures.IntegralHom
