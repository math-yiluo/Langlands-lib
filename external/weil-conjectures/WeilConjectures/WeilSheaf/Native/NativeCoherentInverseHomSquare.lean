/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.SixFunctors.CanonicalOrdinaryRingedTensorCoherence
public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
public import WeilConjectures.WeilSheaf.NativeFrobeniusRingedModel.NativeActionSiteHomComparison
import WeilConjectures.WeilSheaf.Native.NativeNormalizedActionHom

/-! # Inverse Hom comparisons across the normalized restriction square

Source: the native ringed bridge's Hom step and equivalence unit/counit identities.
-/

@[expose] public section
set_option autoImplicit false
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

private theorem normalizedInverseHomComparison_map
    {A B : Type*} [Category A] [Category B] (E : B ≌ A)
    (HA : Aᵒᵖ × A ⥤ A) (HB : Bᵒᵖ × B ⥤ B)
    (h : HB ⋙ E.functor ≅ E.functor.op.prod E.functor ⋙ HA) (X Y : A) :
    E.functor.map ((normalizedInverseHomComparison E HA HB h).hom.app (op X, Y)) ≫
        h.hom.app (op (E.inverse.obj X), E.inverse.obj Y) =
      E.counitIso.hom.app (HA.obj (op X, Y)) ≫
        HA.map (Prod.mkHom (E.counitIso.hom.app X).op (E.counitIso.inv.app Y)) := by
  dsimp [normalizedInverseHomComparison]
  simp only [Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc]
  rw [← E.counit_app_functor]
  rw [E.counit_naturality_assoc]
  simp only [Iso.inv_hom_id_app]
  change E.functor.map (E.inverse.map (HA.map
      (Prod.mkHom (E.counitIso.hom.app X).op (E.counitIso.inv.app Y)))) ≫
        E.counitIso.hom.app _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact E.counit_naturality _

attribute [local irreducible] normalizedInverseHomComparison

/-- Transport the specified Hom comparisons through inverse equivalences.
Source: native ringed bridge step 2; normalized action-site Hom comparison.
(blueprint: new-sf-native-coherent-inverse-hom-square).

Proof: retain the supplied ordinary coherence for the explicit inverse Hom comparison.
Take the square to be the ordinary equivalence unit followed by the
ordinary inverse image of the native equivalence counit. Transport both forward
Hom comparisons through the inverse equivalences. Apply the faithful ordinary
equivalence to the required equation. Naturality of the forward Hom comparison
and the inverse-Hom normalization formula reduce it to naturality of Hom
precomposition. Combine the source maps and target maps separately. The unit
and counit identities identify each with the ordinary counit or its inverse.
The ordinary coherence property is retained unchanged; the square calculation
itself uses no tensor or complex calculation. -/
theorem native_coherent_inverse_hom_square
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    (A : NativeFrobeniusRingedModel k₀ l X)
    (hA : FrobeniusOrdinaryTensorCoherence A)
    (P : TwistedActionRingedSite.Presentation A.J A.s A.R A.a) :
    letI := P.category
    letI := A.additive
    letI : A.E.symm.functor.Additive := A.E.inverse_additive
    let U := P.modules.functor ⋙ TwistedActionRingedSite.forgetPairs
      (TwistedActionRingedSite.sigma A.J A.s A.R A.a)
    ∀ K : TwistedActionRingedSite.Modules P.coefficient ≌ ProEtaleWeilSheaf k₀ l X,
      K.functor = A.toWeil P →
    ∃ square : K.inverse ⋙ U ≅
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ⋙ A.E.inverse,
    ∃ nativeHom : Functor.uncurry.obj (ihomBifunctor k₀ l X) ⋙ K.inverse ≅
        (K.inverse.op.prod K.inverse) ⋙
          Functor.uncurry.obj (SheafOfModules.homFunctor (R := P.coefficient)),
    ∃ ordinaryHom : Functor.uncurry.obj
        (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ⋙
          A.E.inverse ≅ (A.E.inverse.op.prod A.E.inverse) ⋙
            Functor.uncurry.obj (SheafOfModules.homFunctor (R := A.R)),
      OrdinaryRingedTensorCoherence l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
        A.J A.R A.E.symm ordinaryHom ∧
      ∀ M N : ProEtaleWeilSheaf k₀ l X,
        U.map (nativeHom.hom.app (op M, N)) ≫
          (P.hom (K.inverse.obj M) (K.inverse.obj N)).hom ≫
          SheafOfModules.homObjMap (R := A.R) (square.inv.app M) (square.hom.app N) ≫
          ordinaryHom.inv.app (op M.carrier, N.carrier) =
        square.hom.app (ihom k₀ l X M N) := by
  let _ := P.category
  let := A.additive
  let : A.E.symm.functor.Additive := A.E.inverse_additive
  dsimp only
  intro K hK
  obtain ⟨F, G, η, ε, htriangle⟩ := K
  change F = A.toWeil P at hK
  subst F
  let K : TwistedActionRingedSite.Modules P.coefficient ≌ ProEtaleWeilSheaf k₀ l X :=
    { functor := A.toWeil P
      inverse := G
      unitIso := η
      counitIso := ε
      functor_unitIso_comp := htriangle }
  let U := P.modules.functor ⋙ TwistedActionRingedSite.forgetPairs
    (TwistedActionRingedSite.sigma A.J A.s A.R A.a)
  let square : K.inverse ⋙ U ≅
      Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ⋙ A.E.inverse :=
    NatIso.ofComponents (fun M ↦ A.E.unitIso.app (U.obj (K.inverse.obj M)) ≪≫
      A.E.inverse.mapIso
        ((Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapIso
          (K.counitIso.app M))) (by
      intro M N f
      change U.map (K.inverse.map f) ≫
          (A.E.unitIso.hom.app (U.obj (K.inverse.obj N)) ≫
            A.E.inverse.map ((K.counitIso.hom.app N).hom.f)) =
        (A.E.unitIso.hom.app (U.obj (K.inverse.obj M)) ≫
            A.E.inverse.map ((K.counitIso.hom.app M).hom.f)) ≫ A.E.inverse.map f.hom.f
      erw [← Category.assoc, ← A.E.unit_naturality]
      simp only [Category.assoc]
      rw [← A.E.inverse.map_comp, ← A.E.inverse.map_comp]
      congr 1
      exact congrArg A.E.inverse.map
        (congrArg (fun g ↦ g.hom.f) (K.counitIso.hom.naturality f)))
  obtain ⟨forwardHom, forwardHom_normalization⟩ := normalized_action_hom A P
  let nativeHom := normalizedInverseHomComparison K
    (Functor.uncurry.obj (ihomBifunctor k₀ l X))
    (Functor.uncurry.obj (SheafOfModules.homFunctor (R := P.coefficient)))
    forwardHom
  let ordinaryForward := frobeniusOrdinaryForwardHom A
  have ordinaryForward_normalization (M N) :
      ordinaryForward.hom.app (op M, N) = (A.hom M N).hom := rfl
  let ordinaryHom := normalizedInverseHomComparison A.E
    (Functor.uncurry.obj
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (Functor.uncurry.obj (SheafOfModules.homFunctor (R := A.R))) ordinaryForward
  have sqc (M : ProEtaleWeilSheaf k₀ l X) :
      A.E.functor.map (square.hom.app M) ≫ A.E.counitIso.hom.app M.carrier =
        (K.counitIso.hom.app M).hom.f := by
    change A.E.functor.map
        (A.E.unitIso.hom.app _ ≫ A.E.inverse.map (K.counitIso.hom.app M).hom.f) ≫ _ = _
    simp only [Functor.map_comp, Category.assoc]
    erw [A.E.counit_naturality]
    erw [← Category.assoc, A.E.functor_unitIso_comp, Category.id_comp]
  have sqinv (M : ProEtaleWeilSheaf k₀ l X) :
      A.E.functor.map (square.inv.app M) ≫ (K.counitIso.hom.app M).hom.f =
        A.E.counitIso.hom.app M.carrier := by
    rw [← sqc M, ← A.E.functor.map_comp_assoc, Iso.inv_hom_id_app,
      A.E.functor.map_id, Category.id_comp]
  have csqinv (M : ProEtaleWeilSheaf k₀ l X) :
      (K.counitIso.inv.app M).hom.f ≫ A.E.functor.map (square.hom.app M) =
        A.E.counitIso.inv.app M.carrier := by
    apply (Iso.cancel_iso_hom_right _ _ (A.E.counitIso.app M.carrier)).mp
    rw [Iso.app_hom, Category.assoc, sqc]
    erw [Iso.inv_hom_id_app]
    exact congrArg (fun f ↦ f.hom.f) (K.counitIso.inv_hom_id_app M)
  refine ⟨square, nativeHom, ordinaryHom, hA, ?_⟩
  intro M N
  change U.map (nativeHom.hom.app (op M, N)) ≫
      (P.hom (K.inverse.obj M) (K.inverse.obj N)).hom ≫
      SheafOfModules.homObjMap (R := A.R) (square.inv.app M) (square.hom.app N) ≫
      ordinaryHom.inv.app (op M.carrier, N.carrier) =
    square.hom.app (ihom k₀ l X M N)
  apply (cancel_mono (ordinaryHom.hom.app (op M.carrier, N.carrier))).mp
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  apply A.E.functor.map_injective
  apply (cancel_mono (A.hom (A.E.inverse.obj M.carrier)
    (A.E.inverse.obj N.carrier)).hom).mp
  simp only [Functor.map_comp, Category.assoc]
  have hn := congrArg (fun f ↦ f.hom.f)
    (normalizedInverseHomComparison_map K
      (Functor.uncurry.obj (ihomBifunctor k₀ l X))
      (Functor.uncurry.obj (SheafOfModules.homFunctor (R := P.coefficient)))
      forwardHom M N)
  have ho := normalizedInverseHomComparison_map A.E
    (Functor.uncurry.obj
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (Functor.uncurry.obj (SheafOfModules.homFunctor (R := A.R)))
    ordinaryForward M.carrier N.carrier
  change A.E.functor.map (U.map (nativeHom.hom.app (op M, N))) ≫
      (forwardHom.hom.app (op (K.inverse.obj M), K.inverse.obj N)).hom.f =
    (K.counitIso.hom.app (ihom k₀ l X M N)).hom.f ≫
      (Mod.ihomMap (K.counitIso.hom.app M).hom.f).app _ ≫
        (ProEtale.AdicSheaf.ihom _).map (K.counitIso.inv.app N).hom.f at hn
  rw [forwardHom_normalization] at hn
  change A.E.functor.map (ordinaryHom.hom.app (op M.carrier, N.carrier)) ≫
      ordinaryForward.hom.app (op (A.E.inverse.obj M.carrier),
        A.E.inverse.obj N.carrier) =
    A.E.counitIso.hom.app ((ProEtale.AdicSheaf.ihom M.carrier).obj N.carrier) ≫
      (Mod.ihomMap (A.E.counitIso.hom.app M.carrier)).app _ ≫
        (ProEtale.AdicSheaf.ihom _).map (A.E.counitIso.inv.app N.carrier) at ho
  rw [ordinaryForward_normalization] at ho
  conv_lhs =>
    arg 2
    arg 2
    erw [A.hom_naturality (square.inv.app M) (square.hom.app N)]
  conv_lhs => erw [reassoc_of% hn]
  conv_rhs =>
    arg 2
    erw [ho]
  conv_rhs => erw [reassoc_of% (sqc (ihom k₀ l X M N))]
  conv_lhs =>
    arg 2
    arg 2
    erw [reassoc_of%
      (Mod.ihomMap (A.E.functor.map (square.inv.app M))).naturality
        (K.counitIso.inv.app N).hom.f]
  conv_lhs =>
    arg 2
    erw [← NatTrans.comp_app_assoc, ← Mod.ihomMap_comp, sqinv]
    arg 2
    erw [← (ProEtale.AdicSheaf.ihom _).map_comp, csqinv]
  rfl

end AlgebraicGeometry.ProEtaleWeilSheaf
