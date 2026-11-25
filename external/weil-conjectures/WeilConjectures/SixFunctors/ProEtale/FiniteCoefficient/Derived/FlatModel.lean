/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.Sites.ReductionFlatModel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

/-!
# Bounded flat models on the pro-étale site

Finite Tor amplitude in `[a, b]` of a bounded constructible complex of pro-étale sheaves is the
same as admitting a bounded flat model concentrated in `[a, b]` (`lemma-flat-models-generators`,
`lemma-flat-models-generators--1`). This is the pro-étale counterpart of
`AlgebraicGeometry.Etale.hasTorAmplitudeIn_iff_exists_flatModel`.

## Main statements

- `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_iff_exists_flatModel`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

variable {X : Scheme.{u}}

namespace ProEtale.DerivedCategory

/-- Blueprint `lemma-flat-models-generators` (also `lemma-flat-models-generators--1`): Bounded flat
model of finite Tor amplitude, on the small pro-étale site.

For `K ∈ D^b_c(X_proét, A)` and integers `a ≤ b` the following are equivalent: `K` has Tor
amplitude in `[a, b]`; and `K` is isomorphic in `D(X_proét, A)` to a bounded complex `P` of flat
pro-étale sheaves with `P^q = 0` for `q ∉ [a, b]`.

A bounded complex of flat sheaves is K-flat, so its derived tensor product with a sheaf is the
tensor product of complexes, concentrated in `[a, b]`. Conversely one truncates a bounded above
flat resolution in degree `a`, whose term in degree `a` is flat by the Tor criterion
(`DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat`). -/
theorem torAmplitudeIn_iff_exists_flatModel (a b : ℤ) (_hab : a ≤ b)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (_hK : DerivedCategory.boundedConstructible A X K) :
    torAmplitudeIn A X a b K ↔
      ∃ P : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ,
        ((∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧ ∀ q : ℤ, ObjectProperty.flat (P.X q)) ∧
          Nonempty (K ≅ (_root_.DerivedCategory.Q).obj P) := by
  refine (_root_.DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat a b K).trans
    ⟨fun ⟨P, h₁, h₂, h₃, ⟨e⟩⟩ ↦ ⟨P, ⟨fun q hq ↦ ?_, h₃⟩, ⟨e.symm⟩⟩,
      fun ⟨P, ⟨h₁, h₂⟩, ⟨e⟩⟩ ↦ ⟨P, ?_, ?_, h₂, ⟨e.symm⟩⟩⟩
  · rcases hq with hq | hq
    · exact P.isZero_of_isStrictlyGE a q hq
    · exact P.isZero_of_isStrictlyLE b q hq
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun q hq ↦ h₁ q (.inl hq)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun q hq ↦ h₁ q (.inr hq)

end ProEtale.DerivedCategory

namespace ProEtale

variable {A} in
/-- For a bounded complex `P` of flat pro-étale sheaves, the derived tensor product
`P ⊗ᴸ F[0]` is computed by the tensor product of complexes `P ⊗ F`
(`DerivedCategory.QObjTensorSingleFunctorObjIso`, stated with
`AlgebraicGeometry.ProEtale.derivedTensor`). -/
noncomputable def derivedTensorQObjSingleFunctorObjIso {a b : ℤ}
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology X) A) ℤ) [P.IsStrictlyGE a]
    [P.IsStrictlyLE b] (hP : ∀ n, ObjectProperty.flat (P.X n))
    (F : Sheaf (Scheme.ProEt.topology X) A) :
    ((derivedTensor A X).obj ((_root_.DerivedCategory.Q).obj P)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F) ≅
      (_root_.DerivedCategory.Q).obj (((tensorRight F).mapHomologicalComplex _).obj P) :=
  _root_.DerivedCategory.QObjTensorSingleFunctorObjIso P
    (CochainComplex.kFlat_of_bounded_of_flat P a b hP) F

variable {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]

-- the instances `WEqualsLocallyBijective` and `HasSheafCompose` on the small pro-étale site
-- take long to synthesize
/-- Blueprint `lem-sf-reduction-flat-model`: Reduction of the flat model, on the small
pro-étale site.

Let `Λ` be Noetherian (for instance `Λ = A_{E,n}`), `I` an ideal (for instance `ϖ^m`, so that
`Λ ⧸ I = A_{E,m}`), `K ∈ D^b_c(X_proét, Λ)` and `P ≅ K` a complex of flat pro-étale sheaves
with `P^q = 0` for `q ∉ [a, b]`. Its termwise reduction `P' = P / I P` is a complex of flat
sheaves of `Λ ⧸ I`-modules vanishing outside `[a, b]`; the reduction
`K_m = K ⊗ᴸ (Λ ⧸ I)` is computed by `P ⊗ (Λ ⧸ I)` and is the restriction of scalars of
`Q(P') ∈ D(X_proét, Λ ⧸ I)`; and `Q(P')` has Tor amplitude in `[a, b]` over `Λ ⧸ I`. -/
theorem flatModel_reduction (I : Ideal Λ) {a b : ℤ}
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    {P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ℤ}
    (hP : (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧ ∀ q : ℤ, ObjectProperty.flat (P.X q))
    (e : K ≅ (_root_.DerivedCategory.Q).obj P) :
    ((∀ q : ℤ, q < a ∨ b < q →
        IsZero ((((Sheaf.quotSMulTop _ I).mapHomologicalComplex _).obj P).X q)) ∧
      ∀ q : ℤ,
        ObjectProperty.flat ((((Sheaf.quotSMulTop _ I).mapHomologicalComplex _).obj P).X q)) ∧
      Nonempty (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj
              (ModuleCat.of Λ (Λ ⧸ I)))) ≅
        (_root_.DerivedCategory.Q).obj
          (((tensorRight ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (Λ ⧸ I)))).mapHomologicalComplex _).obj P)) ∧
      Nonempty ((Sheaf.restrictScalars (Scheme.ProEt.topology X)
          (Ideal.Quotient.mk I)).mapDerivedCategory.obj ((_root_.DerivedCategory.Q).obj
            (((Sheaf.quotSMulTop _ I).mapHomologicalComplex _).obj P)) ≅
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj
              (ModuleCat.of Λ (Λ ⧸ I))))) ∧
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} (Λ ⧸ I)) X a b
        ((_root_.DerivedCategory.Q).obj
          (((Sheaf.quotSMulTop _ I).mapHomologicalComplex _).obj P)) := by
  obtain ⟨h₁, h₂⟩ := hP
  have : P.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun q hq ↦ h₁ q (.inl hq)
  have : P.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun q hq ↦ h₁ q (.inr hq)
  obtain ⟨hGE, hLE, hflat, htor, ⟨e'⟩⟩ := Sheaf.flatModel_quotSMulTop I (a := a) (b := b) P h₂
  have e₂ := ((derivedTensor _ X).mapIso e).app _ ≪≫
    derivedTensorQObjSingleFunctorObjIso (a := a) (b := b) P h₂
      ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ I)))
  refine ⟨⟨fun q hq ↦ ?_, hflat⟩, ⟨e₂⟩, ⟨e' ≪≫ e₂.symm⟩, htor⟩
  rcases hq with hq | hq
  · exact CochainComplex.isZero_of_isStrictlyGE _ a q hq
  · exact CochainComplex.isZero_of_isStrictlyLE _ b q hq

end ProEtale

end AlgebraicGeometry
