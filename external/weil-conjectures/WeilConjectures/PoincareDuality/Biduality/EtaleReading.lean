/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.DualFullyFaithful
public import WeilConjectures.PoincareDuality.Biduality.EtaleReadingHom
public import WeilConjectures.PoincareDuality.Biduality.EtaleReductionDualizing
public import WeilConjectures.PoincareDuality.Biduality.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality

/-!
# Finite-coefficient biduality on the pro-étale site from the étale site

Let `Λ = 𝒪_E ⧸ ℓⁿ` and write `ρ_X = Rν_* ∘ Φ : D(Mod_{Λ_X}) ⥤ D(X_ét, Λ)` for the étale reading of
condensed `Λ`-module objects (`ProEtale.CondensedRing.finiteEtaleReading` on bounded constructible
complexes). This file proves the finite step (i) of blueprint `theorem-verdier-biduality` for
the reductions `R K₀` of bounded constructible `𝒪_E`-complexes `K₀`: the étale reading is fully
faithful on them, carries `R ω_{X, 𝒪_E}` to the étale dualizing complex and commutes with the
internal homs into it, so the condensed Verdier dual `RHom(-, R ω_{X, 𝒪_E})` is fully faithful on
these objects as soon as the étale one is on their étale readings, which is étale Verdier
biduality. A fully faithful self-adjoint dual has invertible double-dual morphisms.

## Main results

- `ProEtale.CondensedRing.isIso_toIhomIhom_integersModPowReductionAmbient_of_etale`: if étale
  Verdier biduality holds on `Dctf(X_ét, Λ)`, then the double-dual morphism of `R K₀` relative to
  `R ω_{X, 𝒪_E}` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ)

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

attribute [local instance] DerivedCategory.braidedCategory'
attribute [local instance] leftDerivedIntegersModPowReductionMonoidal

/-- The reduction modulo `ℓⁿ` commutes with internal homs of bounded constructible
`𝒪_E`-complexes: `R RHom(K, L) ≅ RHom(R K, R L)`, the comparison
`CategoryTheory.Functor.LaxMonoidal.ihomComparison` being invertible
(`ProEtale.CondensedRing.isIso_ihomComparison_integersModPowReduction`). -/
noncomputable def integersModPowReductionIhomIso
    (K L : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj ((ihom K).obj L)).obj ≅
      (ihom ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj K).obj).obj
        ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj L).obj :=
  haveI := isIso_ihomComparison_integersModPowReduction ℓ E n X K L
  asIso ((Functor.LaxMonoidal.ihomComparison
    L(Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)) K.obj).app L.obj)

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The étale reading `ρ_X` is fully faithful on bounded constructible condensed
`𝒪_E ⧸ ℓⁿ`-complexes, up to isomorphism
(`ProEtale.CondensedRing.finiteEtaleReadingFullyFaithful`). -/
lemma bijective_ambientEtaleReading_map {A B : DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.integersModPowRingObj ℓ E.1 n) X.left))}
    {a b : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E.1 n⟧} (e : a.obj ≅ A)
    (e' : b.obj ≅ B) :
    Function.Bijective (fun f : A ⟶ B ↦ (ambientEtaleReading ℓ E.1 n X).map f) := by
  refine (ambientEtaleReading ℓ E.1 n X).bijective_map_of_iso e e' ?_
  rw [← Function.Bijective.of_comp_iff _ ((ObjectProperty.fullyFaithfulι _).map_bijective a b)]
  exact (finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E.1 n X)).map_bijective a b

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- Naturality of the identification `ρ_X RHom(A, W) ≅ RHom(ρ_X A, Ω)` obtained from
`ProEtale.CondensedRing.finiteEtaleReadingIhomIso` and an isomorphism `ρ_X W ≅ Ω`. -/
lemma finiteEtaleReadingIhomIso_trans_hom_naturality
    {A A' W : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E.1 n⟧} (f : A.obj ⟶ A'.obj)
    {Ω : DerivedCategory (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)))}
    (eω : (finiteEtaleReading ℓ E.1 n X).obj W ≅ Ω) :
    (ambientEtaleReading ℓ E.1 n X).map ((pre f).app W.obj) ≫
        (finiteEtaleReadingIhomIso ℓ E.1 n X A W ≪≫
          (ihom ((finiteEtaleReading ℓ E.1 n X).obj A)).mapIso eω).hom =
      (finiteEtaleReadingIhomIso ℓ E.1 n X A' W ≪≫
          (ihom ((finiteEtaleReading ℓ E.1 n X).obj A')).mapIso eω).hom ≫
        (pre ((finiteEtaleReading ℓ E.1 n X).map (ObjectProperty.homMk f))).app Ω := by
  have h := finiteEtaleReadingIhomIso_hom_naturality ℓ E.1 n X (ObjectProperty.homMk f) W
  have h₂ := ((pre ((finiteEtaleReading ℓ E.1 n X).map (ObjectProperty.homMk f))).naturality
    eω.hom).symm
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The condensed Verdier dual `D = RHom(-, W)` is bijective on morphisms `t ⟶ a` of bounded
constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes as soon as the étale reading `ρ_X` is bijective on
morphisms `D a ⟶ D t` and the étale double-dual morphism of `ρ_X a` relative to `Ω ≅ ρ_X W` is
an isomorphism: through `ρ_X`, which carries `D` to `RHom(-, Ω)`
(`ProEtale.CondensedRing.finiteEtaleReadingIhomIso`), `D` becomes the étale dual on morphisms
`ρ_X t ⟶ ρ_X a`, which is bijective (`CategoryTheory.MonoidalClosed.bijective_pre_app_of_isIso`). -/
lemma bijective_pre_app_of_finiteEtaleReading
    {a t W : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E.1 n⟧}
    {Ω : DerivedCategory (Sheaf X.left.smallEtaleTopology
      (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)))}
    (eω : (finiteEtaleReading ℓ E.1 n X).obj W ≅ Ω)
    [IsIso (toIhomIhom Ω ((finiteEtaleReading ℓ E.1 n X).obj a))]
    (hρ : Function.Bijective (fun g : (ihom a.obj).obj W.obj ⟶ (ihom t.obj).obj W.obj ↦
      (ambientEtaleReading ℓ E.1 n X).map g)) :
    Function.Bijective (fun f : t.obj ⟶ a.obj ↦ (pre f).app W.obj) := by
  have hcomp : (fun g ↦ (ambientEtaleReading ℓ E.1 n X).map g) ∘
      (fun f : t.obj ⟶ a.obj ↦ (pre f).app W.obj) =
      ((finiteEtaleReadingIhomIso ℓ E.1 n X a W ≪≫
          (ihom ((finiteEtaleReading ℓ E.1 n X).obj a)).mapIso eω).symm.homCongr
        (finiteEtaleReadingIhomIso ℓ E.1 n X t W ≪≫
          (ihom ((finiteEtaleReading ℓ E.1 n X).obj t)).mapIso eω).symm) ∘
        (fun g ↦ (pre g).app Ω) ∘ (fun g ↦ (finiteEtaleReading ℓ E.1 n X).map g) ∘
          (ObjectProperty.homMk (X := t) (Y := a)) := by
    funext f
    exact ((Iso.eq_comp_inv _).2
      (finiteEtaleReadingIhomIso_trans_hom_naturality ℓ E n f eω)).trans (Category.assoc _ _ _)
  rw [← Function.Bijective.of_comp_iff' hρ, hcomp]
  exact (Equiv.bijective _).comp <| (bijective_pre_app_of_isIso Ω _ _).comp <|
    ((finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E.1 n X)).map_bijective _ _).comp
      ⟨fun f g h ↦ congrArg InducedCategory.Hom.hom h, ObjectProperty.homMk_surjective⟩

/-- Étale Verdier biduality at the étale reading `ρ_X R K = red_X K` of the reduction of a
bounded constructible `𝒪_E`-complex, which lies in `Dctf`
(`ProEtale.CondensedRing.boundedConstructibleFiniteTor_etaleReduction`). -/
lemma isIso_toIhomIhom_finiteEtaleReading_integersModPowReduction
    (hét : ∀ {M : DerivedCategory (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)))},
      Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)) X.left M →
      IsIso ((Etale.verdierDualDoubleDual (integersModPowCoeff.{u} ℓ E.1 n) X.hom).app M))
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    IsIso (toIhomIhom (Etale.dualizingComplex (integersModPowCoeff.{u} ℓ E.1 n) X.hom)
      ((finiteEtaleReading ℓ E.1 n X).obj
        ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj K))) := by
  have := hét (boundedConstructibleFiniteTor_etaleReduction ℓ E.1 n K)
  rwa [Etale.verdierDualDoubleDual_app] at this

/-- The Verdier dual `D = RHom(-, R ω_{X, 𝒪_E})` is bijective on morphisms `R L ⟶ R K` between
reductions of bounded constructible `𝒪_E`-complexes, assuming étale Verdier biduality
(`ProEtale.CondensedRing.bijective_pre_app_of_finiteEtaleReading`; the duals `D (R K)` are the
reductions `R RHom(K, ω_{X, 𝒪_E})`, on which `ρ_X` is fully faithful). -/
lemma bijective_pre_app_integersModPowReduction
    (hét : ∀ {M : DerivedCategory (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)))},
      Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)) X.left M →
      IsIso ((Etale.verdierDualDoubleDual (integersModPowCoeff.{u} ℓ E.1 n) X.hom).app M))
    (L K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    Function.Bijective (fun f : ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
          L).obj ⟶ ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj K).obj ↦
        (pre f).app ((boundedConstructibleIntegersModPowReduction X.left ℓ E.1 n).obj
          (PadicIntegersRingObj.dualizingComplex ℓ E.1 X)).obj) :=
  have := isIso_toIhomIhom_finiteEtaleReading_integersModPowReduction ℓ E n hét K
  bijective_pre_app_of_finiteEtaleReading ℓ E n (etaleReductionDualizingComplexIso ℓ E.1 n X)
    (bijective_ambientEtaleReading_map ℓ E n
      (integersModPowReductionIhomIso ℓ E n K (PadicIntegersRingObj.dualizingComplex ℓ E.1 X))
      (integersModPowReductionIhomIso ℓ E n L (PadicIntegersRingObj.dualizingComplex ℓ E.1 X)))

/-- **Finite-coefficient biduality on the reductions of integral complexes** (blueprint
`theorem-verdier-biduality`, (i)): if étale Verdier biduality holds on `Dctf(X_ét, Λ)`,
`Λ = 𝒪_E ⧸ ℓⁿ`, then for every bounded constructible `𝒪_E`-complex `K₀` the double-dual morphism
of its reduction `R K₀`, relative to the reduction `R ω_{X, 𝒪_E}` of the integral dualizing
complex, is an isomorphism. -/
theorem isIso_toIhomIhom_integersModPowReductionAmbient_of_etale
    (hét : ∀ {M : DerivedCategory (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)))},
      Etale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E.1 n)) X.left M →
      IsIso ((Etale.verdierDualDoubleDual (integersModPowCoeff.{u} ℓ E.1 n) X.hom).app M))
    (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    IsIso (toIhomIhom
      ((integersModPowReductionAmbient ℓ E n X).obj (PadicIntegersRingObj.dualizingComplex ℓ E.1 X))
      ((integersModPowReductionAmbient ℓ E n X).obj K₀)) := by
  -- the double dual of `R K₀` is the reduction of the double dual of `K₀`
  have e := preIso _
      (integersModPowReductionIhomIso ℓ E n K₀ (PadicIntegersRingObj.dualizingComplex ℓ E.1 X)) ≪≫
    (integersModPowReductionIhomIso ℓ E n
      ((ihom K₀).obj (PadicIntegersRingObj.dualizingComplex ℓ E.1 X))
      (PadicIntegersRingObj.dualizingComplex ℓ E.1 X)).symm
  have h := isIso_toIhomIhom_of_bijective _ _
    (bijective_pre_app_integersModPowReduction ℓ E n hét K₀ K₀)
    (bijective_pre_app_of_iso _ e _ (bijective_pre_app_integersModPowReduction ℓ E n hét
      ((ihom ((ihom K₀).obj (PadicIntegersRingObj.dualizingComplex ℓ E.1 X))).obj
        (PadicIntegersRingObj.dualizingComplex ℓ E.1 X)) K₀))
  exact h

end AlgebraicGeometry.ProEtale.CondensedRing
