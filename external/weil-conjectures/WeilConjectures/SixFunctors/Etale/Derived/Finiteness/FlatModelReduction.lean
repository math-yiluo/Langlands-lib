/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.ReductionFlatModel
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-!
# Reduction of a bounded flat model on the étale site

If `P` is a bounded flat model in degrees `[a, b]` of `K ∈ D(X_ét, Λ)`, its termwise reduction
`P / I P` is a bounded flat model in degrees `[a, b]` of the reduction `K_m = K ⊗ᴸ (Λ ⧸ I)`,
over `Λ ⧸ I` (`lem-sf-reduction-flat-model`).

## Main statements

- `AlgebraicGeometry.Etale.reductionModIdeal_flatModel`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

section

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- For a bounded complex `P` of flat étale sheaves, the derived tensor product `P ⊗ᴸ F[0]` is
computed by the tensor product of complexes `P ⊗ F`. This is
`DerivedCategory.QObjTensorSingleFunctorObjIso`, stated with
`AlgebraicGeometry.Etale.derivedTensor` so that it specialises to `A = ModuleCat Λ` without
comparing monoidal instances. -/
noncomputable def derivedTensorQObjSingleFunctorObjIso {a b : ℤ}
    (P : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hP : ∀ n, ObjectProperty.flat (P.X n)) (F : Sheaf X.smallEtaleTopology A) :
    ((derivedTensor A X).obj ((_root_.DerivedCategory.Q).obj P)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F) ≅
      (_root_.DerivedCategory.Q).obj (((tensorRight F).mapHomologicalComplex _).obj P) :=
  _root_.DerivedCategory.QObjTensorSingleFunctorObjIso P
    (CochainComplex.kFlat_of_bounded_of_flat P a b hP) F

end

variable {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ] {X : Scheme.{u}}

-- the instances `WEqualsLocallyBijective` and `HasSheafCompose` on the small étale site take
-- long to synthesize
/-- Blueprint `lem-sf-reduction-flat-model`: Reduction of the flat model.

Let `Λ` be Noetherian (for instance `Λ = A_{E,n}`), `I` an ideal (for instance `ϖ^m`, so that
`Λ ⧸ I = A_{E,m}`), `K ∈ D^b_c(X_ét, Λ)` and `P ≅ K` a bounded flat model of `K` in degrees
`[a, b]`. Let `P' = P / I P` be the termwise reduction, a complex of sheaves of
`Λ ⧸ I`-modules. Then

* `P'` is a bounded flat model in degrees `[a, b]`: each `P'^q` is a flat sheaf of
  `Λ ⧸ I`-modules and `P'^q = 0` for `q ∉ [a, b]`;
* the reduction `K_m = K ⊗ᴸ (Λ ⧸ I)` (`AlgebraicGeometry.Etale.reductionModIdeal`) is computed
  by the tensor product of complexes `P ⊗ (Λ ⧸ I)`;
* `K_m` is the restriction of scalars of `Q(P') ∈ D(X_ét, Λ ⧸ I)`;
* consequently `Q(P')`, the reduction `K_m` read over `Λ ⧸ I`, has Tor amplitude in `[a, b]`.

`P` is K-flat, so `K ⊗ᴸ (Λ ⧸ I)` is `P ⊗ (Λ ⧸ I)`, which is `P'` with scalars restricted; the
terms of `P'` are flat by the relation criterion for flatness
(`CategoryTheory.Sheaf.flat_quotSMulTop_obj`), and a bounded complex of flat sheaves in degrees
`[a, b]` has Tor amplitude in `[a, b]`. -/
theorem reductionModIdeal_flatModel (I : Ideal Λ) {a b : ℤ}
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    {P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ}
    (hP : IsBoundedFlatComplex Λ a b P) (e : K ≅ (_root_.DerivedCategory.Q).obj P) :
    IsBoundedFlatComplex (Λ ⧸ I) a b
        (((Sheaf.quotSMulTop _ I).mapHomologicalComplex _).obj P) ∧
      Nonempty ((reductionModIdeal Λ X I).obj K ≅ (_root_.DerivedCategory.Q).obj
        (((tensorRight ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Λ ⧸ I)))).mapHomologicalComplex _).obj P)) ∧
      Nonempty ((Sheaf.restrictScalars X.smallEtaleTopology
          (Ideal.Quotient.mk I)).mapDerivedCategory.obj ((_root_.DerivedCategory.Q).obj
            (((Sheaf.quotSMulTop _ I).mapHomologicalComplex _).obj P)) ≅
        (reductionModIdeal Λ X I).obj K) ∧
      DerivedCategory.hasTorAmplitudeIn (Λ ⧸ I) X a b ((_root_.DerivedCategory.Q).obj
        (((Sheaf.quotSMulTop _ I).mapHomologicalComplex _).obj P)) := by
  obtain ⟨h₁, h₂, h₃⟩ := isBoundedFlatComplex_iff.1 hP
  obtain ⟨hGE, hLE, hflat, htor, ⟨e'⟩⟩ := Sheaf.flatModel_quotSMulTop I (a := a) (b := b) P h₃
  have e₂ : (reductionModIdeal Λ X I).obj K ≅ (_root_.DerivedCategory.Q).obj
      (((tensorRight ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ I)))).mapHomologicalComplex _).obj P) :=
    ((derivedTensor _ X).mapIso e).app _ ≪≫
      derivedTensorQObjSingleFunctorObjIso (a := a) (b := b) P h₃ _
  exact ⟨isBoundedFlatComplex_iff.2 ⟨hGE, hLE, hflat⟩, ⟨e₂⟩, ⟨e' ≪≫ e₂.symm⟩,
    DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 htor⟩

end Etale

end AlgebraicGeometry
