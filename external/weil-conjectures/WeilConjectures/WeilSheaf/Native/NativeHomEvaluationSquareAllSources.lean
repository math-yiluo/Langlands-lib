/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import all WeilConjectures.WeilSheaf.DerivedHomPrecomposition
import all WeilConjectures.WeilSheaf.DerivedHom
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all WeilConjectures.Algebra.Homology.BifunctorHomCone
import all WeilConjectures.Algebra.Homology.BifunctorHomComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra

/-! # Hom representative comparison with an unrestricted source -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

namespace TensorEvaluationFormal
universe a b
variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : CoefficientClosedStructure H)

private theorem isIso_pair {C E : Type a} [Category.{b} C] [Category.{b} E]
    {A B : C} {P Q : E} (f : A ⟶ B) (g : P ⟶ Q) [IsIso f] [IsIso g] :
    IsIso (Prod.mkHom f g) :=
  (CategoryTheory.isIso_prod_iff (f := Prod.mkHom f g)).mpr ⟨inferInstance, inferInstance⟩

private theorem hom_naturality {E : Type a} [Category.{b} E]
    {H' : Eᵒᵖ × E ⥤ E} (F : D ⥤ E)
    (χ : H ⋙ F ≅ F.op.prod F ⋙ H') {A B : D} (f : A ⟶ B) (I : D) :
    F.map (H.map (Prod.mkHom f.op (𝟙 I))) ≫ χ.hom.app (op A, I) =
      χ.hom.app (op B, I) ≫ H'.map (Prod.mkHom (F.map f).op (𝟙 (F.obj I))) := by
  simpa using χ.hom.naturality (Prod.mkHom f.op (𝟙 I))

private theorem paste_hom_square
    {Z₀ Z₁ H₀ H₁ B₀ B₁ C₀ C₁ D₀ D₁ E₀ E₁ : D}
    (g : Z₁ ⟶ Z₀) [Epi g]
    (c₀ : Z₀ ⟶ H₀) (c₁ : Z₁ ⟶ H₁) (d : H₁ ⟶ H₀)
    (d₀ : H₀ ⟶ B₀) (d₁ : H₁ ⟶ B₁) (b₀ : B₁ ⟶ B₀)
    (m₀ : B₀ ⟶ E₀) (m₁ : B₁ ⟶ E₁) (b : E₁ ⟶ E₀)
    (v₀ : Z₀ ⟶ C₀) (v₁ : Z₁ ⟶ C₁) (a : C₁ ⟶ C₀)
    (w₀ : C₀ ⟶ D₀) (w₁ : C₁ ⟶ D₁) (u : D₁ ⟶ D₀)
    (r₀ : D₀ ⟶ E₀) (r₁ : D₁ ⟶ E₁)
    (hg : g ≫ c₀ = c₁ ≫ d) (hd : d ≫ d₀ = d₁ ≫ b₀)
    (hb : b₀ ≫ m₀ = m₁ ≫ b)
    (hs : c₁ ≫ d₁ ≫ m₁ = v₁ ≫ w₁ ≫ r₁)
    (ha : g ≫ v₀ = v₁ ≫ a) (hw : a ≫ w₀ = w₁ ≫ u)
    (hr : u ≫ r₀ = r₁ ≫ b) : c₀ ≫ d₀ ≫ m₀ = v₀ ≫ w₀ ≫ r₀ := by
  apply (cancel_epi g).mp
  calc
    _ = c₁ ≫ d₁ ≫ m₁ ≫ b := by
      rw [← Category.assoc g, hg]
      simp only [Category.assoc]
      rw [← Category.assoc d, hd]
      simp only [Category.assoc]
      rw [hb]
    _ = v₁ ≫ w₁ ≫ r₁ ≫ b := by rw [reassoc_of% hs]
    _ = _ := by
      rw [← Category.assoc g, ha]
      simp only [Category.assoc]
      rw [← Category.assoc a, hw]
      simp only [Category.assoc]
      rw [hr]

end TensorEvaluationFormal

namespace TensorEvaluation
variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

private noncomputable abbrev U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)

private noncomputable abbrev UC := (U (k₀ := k₀) (l := l) (X := X)).mapHomologicalComplex (.up ℤ)

private noncomputable abbrev HW := ihomBifunctor k₀ l X

private noncomputable abbrev HO :=
  ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber

private noncomputable def homObjIso (P I : ProEtaleWeilSheaf k₀ l X) :
    (U).obj (((HW).obj (op P)).obj I) ≅ ((HO).obj (op ((U).obj P))).obj ((U).obj I) :=
  Iso.refl _

private theorem homObjIso_right (P I J : ProEtaleWeilSheaf k₀ l X) (f : I ⟶ J) :
    (U).map (((HW).obj (op P)).map f) ≫ (homObjIso P J).hom =
      (homObjIso P I).hom ≫ ((HO).obj (op ((U).obj P))).map ((U).map f) := by
  simp only [homObjIso, Iso.refl_hom, Category.comp_id, Category.id_comp]
  rfl

private theorem homObjIso_left (P Q I : ProEtaleWeilSheaf k₀ l X) (f : Q ⟶ P) :
    (U).map (((HW).map f.op).app I) ≫ (homObjIso Q I).hom =
      (homObjIso P I).hom ≫ ((HO).map ((U).map f).op).app ((U).obj I) := by
  simp only [homObjIso, Iso.refl_hom, Category.comp_id, Category.id_comp]
  rfl

private noncomputable def homIso
    (P I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    (UC).obj (CochainComplex.bifunctorHomObj (HW) P I) ≅
      CochainComplex.bifunctorHomObj (HO) ((UC).obj P) ((UC).obj I) :=
  PrecompositionTransport.complexIso (U) (HW) (HO) homObjIso homObjIso_right homObjIso_left P I

private theorem homIso_projection
    (P I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (n p q : ℤ) (hpq : p + n = q) :
    (homIso P I).hom.f n ≫
        CochainComplex.bifunctorHomπ (HO) ((UC).obj P) ((UC).obj I) n p q hpq =
      (U).map (CochainComplex.bifunctorHomπ (HW) P I n p q hpq) := by
  change (PrecompositionTransport.component (U) (HW) (HO) homObjIso P I n).hom ≫ _ = _
  simpa only [homObjIso, Iso.refl_hom, Category.comp_id] using
    PrecompositionTransport.component_π (U) (HW) (HO) homObjIso P I n p q hpq

private theorem homIso_left
    {P J I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (a : P ⟶ J) :
    (UC).map (CochainComplex.bifunctorHomMapLeft (H := HW) (Y := I) a) ≫
        (homIso P I).hom =
      (homIso J I).hom ≫ CochainComplex.bifunctorHomMapLeft
        (H := HO) (Y := (UC).obj I) ((UC).map a) :=
  PrecompositionTransport.complexIso_left (U) (HW) (HO) homObjIso homObjIso_right homObjIso_left a

attribute [local irreducible] homIso

private theorem hom_square
    (M : NativeClosedHomModels k₀ l X)
    (χ : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (hχ : NativeHomRepresentativeCompatibility (HW) (HO)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives (U) χ)
    (P I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : P.IsKInjective) (hI : I.IsKInjective)
    (hUI : CochainComplex.IsKInjective ((UC).obj I)) :
      χ.hom.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) ≫
          M.ordinaryHom.map (Prod.mkHom ((U).mapDerivedCategoryFactors.inv.app P).op
            ((U).mapDerivedCategoryFactors.hom.app I)) ≫
          (M.ordinaryRepresentatives.model _ _ hUI).hom =
        (nativeForget k₀ l X).map (M.weilRepresentatives.model P I hI).hom ≫
          (U).mapDerivedCategoryFactors.hom.app
            (CochainComplex.bifunctorHomObj (HW) P I) ≫
          DerivedCategory.Q.map (homIso P I).hom := by
  obtain ⟨_, hUI', c, hc, hs⟩ := hχ P I hP hI
  have he : c.hom = (homIso P I).hom := by
    apply HomologicalComplex.hom_ext
    intro n
    apply CochainComplex.bifunctorHomObj_hom_ext
    intro p q hpq
    exact (eq_of_heq (hc n p q hpq)).trans (homIso_projection P I n p q hpq).symm
  simpa only [he, Iso.app_hom, UC, HO, nativeForget] using hs

-- Instantiating all representative naturality squares involves several localization functors.
private theorem hom_square_all
    (M : NativeClosedHomModels k₀ l X)
    (χ : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (hχ : NativeHomRepresentativeCompatibility (HW) (HO)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives (U) χ)
    (P I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hI : I.IsKInjective) (hUI : CochainComplex.IsKInjective ((UC).obj I)) :
      χ.hom.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) ≫
          M.ordinaryHom.map (Prod.mkHom ((U).mapDerivedCategoryFactors.inv.app P).op
            ((U).mapDerivedCategoryFactors.hom.app I)) ≫
          (M.ordinaryRepresentatives.model _ _ hUI).hom =
        (nativeForget k₀ l X).map (M.weilRepresentatives.model P I hI).hom ≫
          (U).mapDerivedCategoryFactors.hom.app
            (CochainComplex.bifunctorHomObj (HW) P I) ≫
          DerivedCategory.Q.map (homIso P I).hom := by
  obtain ⟨J, hJ, a, _, ha⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective P
  let := ha
  have hs := hom_square M χ hχ J I hJ hI hUI
  let F := nativeForget k₀ l X
  let δ := (U (k₀ := k₀) (l := l) (X := X)).mapDerivedCategoryFactors
  let A := CochainComplex.bifunctorHomMapLeft (H := HW) (Y := I) a
  let B := CochainComplex.bifunctorHomMapLeft (H := HO) (Y := (UC).obj I) ((UC).map a)
  let g := F.map (M.weilHom.map
    (Prod.mkHom (DerivedCategory.Q.map a).op (𝟙 (DerivedCategory.Q.obj I))))
  have : IsIso (DerivedCategory.Q.map a) := inferInstance
  have : IsIso (Prod.mkHom (DerivedCategory.Q.map a).op
      (𝟙 (DerivedCategory.Q.obj I))) :=
    TensorEvaluationFormal.isIso_pair (DerivedCategory.Q.map a).op (𝟙 _)
  have : IsIso g := inferInstanceAs (IsIso (F.map (M.weilHom.map
    (Prod.mkHom (DerivedCategory.Q.map a).op (𝟙 (DerivedCategory.Q.obj I))))))
  have hA := M.weilRepresentatives.naturality P J I I hI hI a (𝟙 I)
  simp only [CochainComplex.bifunctorHomMapRight_id,
    Category.comp_id] at hA
  rw [DerivedCategory.Q.map_id I] at hA
  have hB := M.ordinaryRepresentatives.naturality ((UC).obj P) ((UC).obj J)
    ((UC).obj I) ((UC).obj I) hUI hUI ((UC).map a) (𝟙 _)
  simp only [CochainComplex.bifunctorHomMapRight_id,
    Category.comp_id] at hB
  rw [DerivedCategory.Q.map_id ((UC).obj I)] at hB
  have hδ : F.map (DerivedCategory.Q.map A) ≫ δ.hom.app _ =
      δ.hom.app _ ≫ DerivedCategory.Q.map ((UC).map A) := δ.hom.naturality A
  have hAB : DerivedCategory.Q.map ((UC).map A) ≫
      DerivedCategory.Q.map (homIso P I).hom =
    DerivedCategory.Q.map (homIso J I).hom ≫ DerivedCategory.Q.map B := by
    simpa only [Functor.map_comp] using congrArg (fun z ↦ DerivedCategory.Q.map z)
      (homIso_left a (I := I))
  have hδa : δ.inv.app P ≫ F.map (DerivedCategory.Q.map a) =
      DerivedCategory.Q.map ((UC).map a) ≫ δ.inv.app J := (δ.inv.naturality a).symm
  have hn := TensorEvaluationFormal.hom_naturality F χ (DerivedCategory.Q.map a)
    (DerivedCategory.Q.obj I)
  have hd : M.ordinaryHom.map
      (Prod.mkHom (F.map (DerivedCategory.Q.map a)).op
        (𝟙 (F.obj (DerivedCategory.Q.obj I)))) ≫
      M.ordinaryHom.map (Prod.mkHom (δ.inv.app P).op (δ.hom.app I)) =
    M.ordinaryHom.map (Prod.mkHom (δ.inv.app J).op (δ.hom.app I)) ≫
      M.ordinaryHom.map
        (Prod.mkHom (DerivedCategory.Q.map ((UC).map a)).op
          (𝟙 (DerivedCategory.Q.obj ((UC).obj I)))) := by
    simp only [← M.ordinaryHom.map_comp]
    congr 1
    apply Prod.ext
    · exact congrArg Quiver.Hom.op hδa
    · simp
  have hAg : g ≫ F.map (M.weilRepresentatives.model P I hI).hom =
      F.map (M.weilRepresentatives.model J I hI).hom ≫
        F.map (DerivedCategory.Q.map A) := by
    simpa only [Functor.map_comp] using congrArg F.map hA
  exact TensorEvaluationFormal.paste_hom_square g
    (χ.hom.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I))
    (χ.hom.app (op (DerivedCategory.Q.obj J), DerivedCategory.Q.obj I))
    (M.ordinaryHom.map (Prod.mkHom (F.map (DerivedCategory.Q.map a)).op
      (𝟙 (F.obj (DerivedCategory.Q.obj I)))))
    (M.ordinaryHom.map (Prod.mkHom (δ.inv.app P).op (δ.hom.app I)))
    (M.ordinaryHom.map (Prod.mkHom (δ.inv.app J).op (δ.hom.app I)))
    (M.ordinaryHom.map (Prod.mkHom (DerivedCategory.Q.map ((UC).map a)).op
      (𝟙 (DerivedCategory.Q.obj ((UC).obj I)))))
    (M.ordinaryRepresentatives.model ((UC).obj P) ((UC).obj I) hUI).hom
    (M.ordinaryRepresentatives.model ((UC).obj J) ((UC).obj I) hUI).hom
    (DerivedCategory.Q.map B)
    (F.map (M.weilRepresentatives.model P I hI).hom)
    (F.map (M.weilRepresentatives.model J I hI).hom) (F.map (DerivedCategory.Q.map A))
    (δ.hom.app (CochainComplex.bifunctorHomObj (HW) P I))
    (δ.hom.app (CochainComplex.bifunctorHomObj (HW) J I))
    (DerivedCategory.Q.map ((UC).map A))
    (DerivedCategory.Q.map (homIso P I).hom) (DerivedCategory.Q.map (homIso J I).hom)
    hn hd hB hs hAg hδ hAB

end TensorEvaluation

/-- The projection-normalized native Hom comparison extends from two K-injective
complexes to an arbitrary source and a K-injective target.

Source: Stacks 0A97; source-replacement step in the representative evaluation
argument for the native tensor model.
(blueprint: lem-sf-native-hom-evaluation-square-all-sources).

Proof: construct the forgotten product-Hom comparison explicitly by its product
projections. The supplied projection condition identifies its witness with this
comparison on K-injective sources. For an arbitrary source choose a monomorphic
quasi-isomorphism to a K-injective complex. Naturality of both representative
systems, the derived factorization, and the canonical comparison propagates the
square to the source; cancel the invertible localized replacement map. -/
theorem native_hom_evaluation_square_all_sources
    (M : NativeClosedHomModels k₀ l X)
    (χ : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (hχ : NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) χ)
    (P I : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (hI : I.IsKInjective) :
    let U₀ := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
    let UC₀ := U₀.mapHomologicalComplex (.up ℤ)
    let H₀ := ihomBifunctor k₀ l X
    let H₁ := ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
    ∃ hUI : CochainComplex.IsKInjective (UC₀.obj I),
    ∃ c : UC₀.obj (CochainComplex.bifunctorHomObj H₀ P I) ≅
      CochainComplex.bifunctorHomObj H₁ (UC₀.obj P) (UC₀.obj I),
      (∀ (n p q : ℤ) (hpq : p + n = q),
        c.hom.f n ≫ CochainComplex.bifunctorHomπ H₁
          (UC₀.obj P) (UC₀.obj I) n p q hpq =
            U₀.map (CochainComplex.bifunctorHomπ H₀ P I n p q hpq)) ∧
      χ.hom.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) ≫
          M.ordinaryHom.map (Prod.mkHom (U₀.mapDerivedCategoryFactors.inv.app P).op
            (U₀.mapDerivedCategoryFactors.hom.app I)) ≫
          (M.ordinaryRepresentatives.model (UC₀.obj P) (UC₀.obj I) hUI).hom =
        (nativeForget k₀ l X).map (M.weilRepresentatives.model P I hI).hom ≫
          U₀.mapDerivedCategoryFactors.hom.app
            (CochainComplex.bifunctorHomObj H₀ P I) ≫ DerivedCategory.Q.map c.hom := by
  obtain ⟨_, hUI, _, _, _⟩ := hχ I I hI hI
  exact ⟨hUI, TensorEvaluation.homIso P I,
    TensorEvaluation.homIso_projection P I,
    TensorEvaluation.hom_square_all M χ hχ P I hI hUI⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
