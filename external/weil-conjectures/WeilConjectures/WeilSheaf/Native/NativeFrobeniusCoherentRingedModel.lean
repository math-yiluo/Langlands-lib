/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.CanonicalOrdinaryRingedTensorCoherence
public import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusComparison
import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomNaturality

/-! # The explicit Frobenius model with ordinary tensor coherence retained -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.TwistedActionRingedSite
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local irreducible] SheafOfModules.monoidalCategory
  ProEtale.NativeFrobenius.equivalence

/-- The canonical Frobenius model, constructed independently of tensor coherence.
Source: the explicit native_frobenius_ringed_model construction
(blueprint: new-sf-native-frobenius-coherent-ringed-model). -/
def canonicalFrobeniusRingedModel
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    NativeFrobeniusRingedModel k₀ l X := by
  classical
  let Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let g := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
  let _ := (ProEtale.NativeFrobenius.translation_continuous Y g).1
  let _ := (ProEtale.NativeFrobenius.translation_continuous Y g).2
  let H := Classical.choice (ProEtale.adicModuleHomComparisonCore l Y)
  let hc := ProEtale.NativeFrobenius.nativeFrobeniusComparison Y l g H
  exact {
    C := WeilConjectures.WeilFrobeniusAction.Site Y
    category := inferInstance
    pullbacks := Adjunction.hasLimitsOfShape_of_equivalence
      (AsSmall.equiv.{u, u + 1, u + 1} :
        Y.ProEt ≌ WeilConjectures.WeilFrobeniusAction.Site Y).inverse
    J := WeilConjectures.WeilFrobeniusAction.topology Y
    s := WeilConjectures.WeilFrobeniusAction.translation g
    R := ProEtale.NativeFrobenius.ring Y l
    a := ProEtale.NativeFrobenius.ringIso Y l g
    E := ProEtale.NativeFrobenius.equivalence Y l
    additive := inferInstance
    comparison := hc.choose
    hom := ProEtale.NativeFrobenius.homComparison Y l H
    hom_naturality := fun f h ↦
      ProEtale.NativeFrobenius.homComparison_naturality Y l H f h
    hom_frobenius := hc.choose_spec }

-- Check the constructor with abstract data so kernel conversion does not expand
-- the concrete equivalence while comparing the two coherence predicates.
-- The two native and ringed module presentations require substantial type conversion.
private theorem coherent_model_mk
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    {C : Type (u + 1)} [SmallCategory C] [HasPullbacks C]
    (J : GrothendieckTopology C) (s : C ≌ C)
    [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u + 1})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u + 1} J J).obj R ≅ R)
    (E : Modules R ≌ ProEtale.AdicSheaf l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    [E.functor.Additive]
    (c : E.functor ⋙ WeilSheaf.frobeniusPullback k₀ l X ≅ sigma J s R a ⋙ E.functor)
    (hom : ∀ M N : Modules R,
      E.functor.obj (SheafOfModules.homObj (R := R) M N) ≅
        (ProEtale.AdicSheaf.ihom (E.functor.obj M)).obj (E.functor.obj N))
    (hn : ∀ {M M' N N' : Modules R} (f : M' ⟶ M) (g : N ⟶ N'),
      E.functor.map (SheafOfModules.homObjMap (R := R) f g) ≫
          (hom M' N').hom =
        (hom M N).hom ≫ (Mod.ihomMap (E.functor.map f)).app _ ≫
          (ProEtale.AdicSheaf.ihom (E.functor.obj M')).map (E.functor.map g))
    (hf : ∀ (P : Presentation J s R a) (M N : Modules R),
      (WeilSheaf.frobeniusPullback k₀ l X).map (hom M N).hom ≫
          (ProEtale.adicLowerStarCompIhomIso l
            (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
            (E.functor.obj M)).inv.app (E.functor.obj N) ≫
          (Mod.ihomMap (c.app M).inv).app _ ≫
            (ProEtale.AdicSheaf.ihom (E.functor.obj ((sigma J s R a).obj M))).map
              (c.app N).hom =
        c.hom.app (SheafOfModules.homObj (R := R) M N) ≫
          E.functor.map (P.sigmaHom M N).hom ≫
          (hom ((sigma J s R a).obj M) ((sigma J s R a).obj N)).hom)
    (hc : letI : E.symm.functor.Additive := E.inverse_additive
      OrdinaryRingedTensorCoherence l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
        J R E.symm (normalizedInverseHomComparison E
          (Functor.uncurry.obj
            (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
          (Functor.uncurry.obj (SheafOfModules.homFunctor (R := R)))
          (NatIso.ofComponents (fun MN ↦ hom MN.1.unop MN.2)
            (fun fg ↦ hn fg.1.unop fg.2)))) :
    FrobeniusOrdinaryTensorCoherence {
      C := C
      J := J
      s := s
      R := R
      a := a
      E := E
      additive := inferInstance
      comparison := c
      hom := hom
      hom_naturality := hn
      hom_frobenius := hf } := by
  let A : NativeFrobeniusRingedModel k₀ l X := {
    C := C
    J := J
    s := s
    R := R
    a := a
    E := E
    additive := inferInstance
    comparison := c
    hom := hom
    hom_naturality := hn
    hom_frobenius := hf }
  change FrobeniusOrdinaryTensorCoherence A
  exact hc

-- The two native and ringed module presentations require substantial type conversion.
/-- Retain tensor coherence of the explicitly constructed canonical Frobenius model.
Source: canonical section tensor comparison
(blueprint: new-sf-native-frobenius-coherent-ringed-model).

Proof: unfold the explicit model's site, equivalence and Hom maps. They are
precisely those of the canonical ordinary coherence theorem for the proved
comparison core. Apply that theorem. The model definition uses no tensor
coherence theorem; this result supplies only its coherence property. -/
theorem native_frobenius_coherent_ringed_model
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    FrobeniusOrdinaryTensorCoherence (canonicalFrobeniusRingedModel k₀ l X) := by
  let Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  let g := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
  let _ := (ProEtale.NativeFrobenius.translation_continuous Y g).1
  let _ := (ProEtale.NativeFrobenius.translation_continuous Y g).2
  let _ : HasPullbacks (WeilConjectures.WeilFrobeniusAction.Site Y) :=
    Adjunction.hasLimitsOfShape_of_equivalence
      (AsSmall.equiv.{u, u + 1, u + 1} :
        Y.ProEt ≌ WeilConjectures.WeilFrobeniusAction.Site Y).inverse
  let H := Classical.choice (ProEtale.adicModuleHomComparisonCore l Y)
  let hc := ProEtale.NativeFrobenius.nativeFrobeniusComparison Y l g H
  let E := ProEtale.NativeFrobenius.equivalence Y l
  let _ : E.symm.functor.Additive := E.inverse_additive
  let h : Functor.uncurry.obj
      (SheafOfModules.homFunctor (R := ProEtale.NativeFrobenius.ring Y l)) ⋙ E.functor ≅
      E.functor.op.prod E.functor ⋙ Functor.uncurry.obj (ordinaryIhomBifunctor l Y) :=
    NatIso.ofComponents
      (fun MN ↦ ProEtale.NativeFrobenius.homComparison Y l H MN.1.unop MN.2)
      (fun fg ↦ ProEtale.NativeFrobenius.homComparison_naturality Y l H fg.1.unop fg.2)
  have hs : canonicalOrdinaryForwardHom l Y H = h := rfl
  have ht := congrArg (fun h ↦ OrdinaryRingedTensorCoherence l Y
    (WeilConjectures.WeilFrobeniusAction.topology Y)
    (ProEtale.NativeFrobenius.ring Y l) E.symm
    (normalizedInverseHomComparison E
      (Functor.uncurry.obj (ordinaryIhomBifunctor l Y))
      (Functor.uncurry.obj
        (SheafOfModules.homFunctor (R := ProEtale.NativeFrobenius.ring Y l))) h)) hs
  exact coherent_model_mk k₀ l X
    (WeilConjectures.WeilFrobeniusAction.topology Y)
    (WeilConjectures.WeilFrobeniusAction.translation g)
    (ProEtale.NativeFrobenius.ring Y l) (ProEtale.NativeFrobenius.ringIso Y l g)
    (ProEtale.NativeFrobenius.equivalence Y l) hc.choose
    (ProEtale.NativeFrobenius.homComparison Y l H)
    (fun f h ↦ ProEtale.NativeFrobenius.homComparison_naturality Y l H f h)
    hc.choose_spec (ht.mp (canonical_ordinary_ringed_tensor_coherence l Y H))


end AlgebraicGeometry.ProEtaleWeilSheaf
