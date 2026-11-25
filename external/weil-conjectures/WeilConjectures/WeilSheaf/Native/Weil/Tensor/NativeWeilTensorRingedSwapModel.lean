/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedModel
public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapComplex
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBinaryModelComparison
import WeilConjectures.CategoryTheory.SixFunctors.TransportedTensorComparison
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorSymmetryRepresentatives

set_option linter.privateModule false

/-! # The signed native chain swap represents the transported derived braiding

Source: Stacks 06YU and 0FPT, the K-flat symmetry model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option linter.style.haveILetI false
set_option cleanup.letToHave false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

@[instance_reducible]
private def transportedSymmetric
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D] [SymmetricCategory D]
    (E : C ≌ D) : @SymmetricCategory C _ (Monoidal.transport E.symm) :=
  inferInstanceAs (SymmetricCategory (Monoidal.Transported E.symm))

private theorem transported_braiding
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D] [SymmetricCategory D]
    (E : C ≌ D) (X Y : C) :
    letI := Monoidal.transport E.symm
    letI := transportedSymmetric E
    let μ := transportedTensorComparison E
    E.functor.map (β_ X Y).hom ≫ μ.hom.app (Y, X) =
      μ.hom.app (X, Y) ≫ (β_ (E.functor.obj X) (E.functor.obj Y)).hom := by
  letI := Monoidal.transport E.symm
  letI := transportedSymmetric E
  letI : E.functor.Monoidal :=
    inferInstanceAs (Monoidal.equivalenceTransported E.symm).inverse.Monoidal
  letI : E.functor.Braided :=
    inferInstanceAs (Monoidal.equivalenceTransported E.symm).inverse.Braided
  change E.functor.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ E.functor Y X =
    Functor.OplaxMonoidal.δ E.functor X Y ≫
      (β_ (E.functor.obj X) (E.functor.obj Y)).hom
  rw [Functor.map_braiding]
  simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

private theorem braiding_of_model_comparison
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.Faithful]
    (μ : MonoidalCategory.tensor C ⋙ F ≅ F.prod F ⋙ MonoidalCategory.tensor D)
    {X Y V W : C} {X' Y' V' W' : D}
    (l : V ≅ X ⊗ Y) (r : W ≅ Y ⊗ X) (a : V ⟶ W)
    (l' : V' ⟶ X' ⊗ Y') (r' : W' ⟶ Y' ⊗ X') (a' : V' ⟶ W')
    (eX : F.obj X ≅ X') (eY : F.obj Y ≅ Y')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (hA : l' ≫ (β_ X' Y').hom = a' ≫ r')
    (hL : F.map l.hom ≫ μ.hom.app (X, Y) ≫ (eX.hom ⊗ₘ eY.hom) = eV ≫ l')
    (hR : F.map r.hom ≫ μ.hom.app (Y, X) ≫ (eY.hom ⊗ₘ eX.hom) = eW ≫ r')
    (hC : F.map a ≫ eW = eV ≫ a')
    (hμ : F.map (β_ X Y).hom ≫ μ.hom.app (Y, X) =
      μ.hom.app (X, Y) ≫ (β_ (F.obj X) (F.obj Y)).hom) :
    l.hom ≫ (β_ X Y).hom = a ≫ r.hom := by
  apply F.map_injective
  apply (cancel_mono (μ.hom.app (Y, X) ≫ (eY.hom ⊗ₘ eX.hom))).1
  simp only [Functor.map_comp, Category.assoc]
  calc
    _ = F.map l.hom ≫ μ.hom.app (X, Y) ≫
        (β_ (F.obj X) (F.obj Y)).hom ≫ (eY.hom ⊗ₘ eX.hom) := by rw [reassoc_of% hμ]
    _ = F.map l.hom ≫ μ.hom.app (X, Y) ≫
        (eX.hom ⊗ₘ eY.hom) ≫ (β_ X' Y').hom := by
      rw [BraidedCategory.braiding_naturality]
      rfl
    _ = eV ≫ l' ≫ (β_ X' Y').hom := by rw [reassoc_of% hL]
    _ = eV ≫ a' ≫ r' := by rw [hA]
    _ = F.map a ≫ eW ≫ r' := by rw [reassoc_of% hC]
    _ = _ := by rw [hR]

private theorem coefficientSymmetry_model_native
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (RingedTensorModules.{u, u, u} J R)]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, u, u, u + 1} J R))
    (B : CoefficientTensorModels.{u, u, u, u + 1} J R S)
    (β : @SymmetricCategory _ _ S.monoidal)
    (c : RingedDerivedTensorCoherence J R S B β)
    (P Q : CochainComplex (RingedTensorModules.{u, u, u} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    letI := S.monoidal
    letI := β
    (c.tensorIso P Q (Or.inr hQ)).hom ≫
        (β_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map (CochainComplex.Monoidal.braiding P Q).hom ≫
        (c.tensorIso Q P (Or.inr hP)).hom := by
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.symmetricCategory R
  letI := S.monoidal
  letI := β
  obtain ⟨s, hs, hm⟩ := c.symmetry_model P Q hP hQ
  have he : s.hom = (CochainComplex.Monoidal.braiding P Q).hom := by
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    change p + q = n at h
    have h' : q + p = n := by omega
    change RingedForgetTensorTransposition.tensorSummand J R P Q p q n h ≫
      s.hom.f n = HomologicalComplex.ιTensorObj P Q p q n h ≫
        (CochainComplex.Monoidal.braiding P Q).hom.f n
    rw [RingedForgetTensorTransposition.swap_summand J R P Q s hs p q n h h']
    simpa only [RingedForgetTensorTransposition.tensorSummand,
      Preadditive.zsmul_comp] using
      (CochainComplex.Monoidal.ι_braiding_hom (K := P) (L := Q) p q n h).symm
  rw [he] at hm
  simpa only [c.tensorIso_both P Q hP hQ, c.tensorIso_both Q P hQ hP] using hm

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)
  (A : NativeWeilRingedTensorComplexes b T adj)

variable [HasDerivedCategory.{u + 2}
    (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
  (SB : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
  (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
  (βB : @SymmetricCategory _ _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)

/-- The explicit native chain swap represents the transported derived braiding.
Source: Stacks 06YU and 0FPT; the ringed symmetry model and monoidal transport.
(blueprint: new-sf-native-weil-ringed-swap-model).

Proof: apply the fully faithful native derived equivalence. Its oplax tensorator
is the transported counit comparison. The two binary model squares identify the
models with the localized ringed comparisons. Apply `cB.symmetry_model` to the
images of P and Q, K-flat by `A.flat`. Its signed generator formula identifies
the supplied swap with the canonical cochain braiding by pure-tensor and coproduct
extensionality. `cB.tensorIso_both` identifies its simultaneous models with the
one-K-flat models. Naturality of the localization factor applied to the defining
square of `nativeRingedSwapComplex` completes the equality; cancel the invertible
model and tensor comparisons and reflect equality through the equivalence. -/
theorem nativeRingedSwapComplex_model
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (hP : NativeTensorKFlat k₀ l X T P) (hQ : NativeTensorKFlat k₀ l X T Q) :
    ((nativeWeilRingedSymmetric b SB βB).toBraidedCategory.braiding
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
      (nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP).hom =
    (nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ).hom ≫
      DerivedCategory.Q.map (nativeRingedSwapComplex b T adj A P Q).hom := by
  classical
  letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
  letI := SheafOfModules.monoidalCategory b.R
  letI := SheafOfModules.symmetricCategory b.R
  letI := SB.monoidal
  letI := βB
  letI := nativeWeilRingedMonoidal b SB
  letI := nativeWeilRingedSymmetric b SB βB
  let E := nativeWeilRingedDerivedEquivalence b
  let Ec := b.native.functor.mapHomologicalComplex (.up ℤ)
  let τ := b.native.functor.mapDerivedCategoryFactors
  let q := DerivedCategory.Q (C := ProEtaleWeilSheaf k₀ l X)
  let qB := DerivedCategory.Q
    (C := RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)
  let μ := nativeRingedTensorComparison b SB
  let s := nativeRingedSwapComplex b T adj A P Q
  let m₀ := nativeWeilRingedTensorModel b T adj A SB TB βB cB Q P hQ
  let m₁ := nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP
  let ci₀ := cB.tensorIso (Ec.obj P) (Ec.obj Q) (Or.inr (A.flat Q hQ))
  let ci₁ := cB.tensorIso (Ec.obj Q) (Ec.obj P) (Or.inr (A.flat P hP))
  let e₀ := τ.hom.app (CochainComplex.mapBifunctor Q P T) ≫
    qB.map (A.chain Q P).hom
  let e₁ := τ.hom.app (CochainComplex.mapBifunctor P Q T) ≫
    qB.map (A.chain P Q).hom
  have hA := coefficientSymmetry_model_native b.J b.R SB TB βB cB
    (Ec.obj P) (Ec.obj Q) (A.flat P hP) (A.flat Q hQ)
  have hL := nativeRingedTensorModel_binary b T adj A SB TB βB cB P Q hQ
  have hR := nativeRingedTensorModel_binary b T adj A SB TB βB cB Q P hP
  have hC : E.functor.map (q.map s.hom) ≫ e₁ =
      e₀ ≫ qB.map (CochainComplex.Monoidal.braiding (Ec.obj P) (Ec.obj Q)).hom :=
    localizationModel_square q qB E.functor Ec τ s.hom (A.chain Q P).hom
      (A.chain P Q).hom
      (CochainComplex.Monoidal.braiding (Ec.obj P) (Ec.obj Q)).hom
      (nativeRingedSwapComplex_square b T adj A P Q)
  have hμ : E.functor.map (β_ (q.obj P) (q.obj Q)).hom ≫ μ.hom.app (q.obj Q, q.obj P) =
      μ.hom.app (q.obj P, q.obj Q) ≫
        (β_ (E.functor.obj (q.obj P)) (E.functor.obj (q.obj Q))).hom :=
    transported_braiding E (q.obj P) (q.obj Q)
  have hh := braiding_of_model_comparison E.functor μ
    m₀.symm m₁.symm (q.map s.hom) ci₀.hom ci₁.hom
    (qB.map (CochainComplex.Monoidal.braiding (Ec.obj P) (Ec.obj Q)).hom)
    (τ.app P) (τ.app Q) e₀ e₁ hA
    (by simpa only [e₀, m₀, ci₀, E, Ec, τ, q, qB, μ, nativeTensorComplex,
      Iso.symm_hom, Iso.app_hom, Category.assoc] using hL)
    (by simpa only [e₁, m₁, ci₁, E, Ec, τ, q, qB, μ, nativeTensorComplex,
      Iso.symm_hom, Iso.app_hom, Category.assoc] using hR) hC hμ
  have hh' := congrArg (fun f ↦ m₀.hom ≫ f ≫ m₁.hom) hh
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using hh'

end AlgebraicGeometry.ProEtaleWeilSheaf
