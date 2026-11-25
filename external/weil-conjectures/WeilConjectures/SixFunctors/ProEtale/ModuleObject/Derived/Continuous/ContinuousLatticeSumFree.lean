/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousLatticeSum
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Internal freeness of continuous finite lattice sums

Source: the continuous lattice sum step in the stratified lattice proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A presentation of an internal module by continuous functions, including its
actual scalar action and restriction maps.
Source: Bhatt--Scholze, Section 6.8, and the continuous coefficient encoding.
(blueprint: def-sfb-continuous-function-module-presentation) -/
structure ContinuousFunctionPresentation (X : Scheme.{u}) (A : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    (N : Type v) [AddCommGroup N] [Module A N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [ContinuousSMul A N]
    (Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X)) where
  sections : ∀ U : X.ProEt,
    ((continuousRingModuleEquivalence X A).functor.obj Q).val.obj (op U) ≃+ C(U.left, N)
  restrict : ∀ (U V : X.ProEt) (a : V ⟶ U)
    (x : ((continuousRingModuleEquivalence X A).functor.obj Q).val.obj (op U)),
    sections V (((continuousRingModuleEquivalence X A).functor.obj Q).val.map a.op x) =
      (sections U x).comp a.left.base.hom
  smul : ∀ (U : X.ProEt) (a : ULift.{u + 1} C(U.left, A))
    (x : ((continuousRingModuleEquivalence X A).functor.obj Q).val.obj (op U)),
    sections U (a • x) = a.down • sections U x

private theorem module_iso_product
    {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (M : SheafOfModules.{u + 1} R) (n : ℕ)
    (e : ∀ U : Cᵒᵖ, M.val.obj U ≃+ (Fin n → R.obj.obj U))
    (he : ∀ (U : Cᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U),
      e U (a • x) = a • e U x)
    (hn : ∀ (U V : Cᵒᵖ) (a : U ⟶ V) (x : M.val.obj U),
      e V (M.val.map a x) = fun i ↦ R.obj.map a (e U x i)) :
    Nonempty (M ≅ ∏ᶜ (fun _ : Fin n ↦ SheafOfModules.unit R)) := by
  let π (i : Fin n) : M ⟶ SheafOfModules.unit R :=
    ⟨{ app U := ModuleCat.ofHom
        { toFun := fun x ↦ e U x i
          map_add' := fun x y ↦ congrFun ((e U).map_add x y) i
          map_smul' := fun a x ↦ congrFun (he U a x) i }
       naturality := fun {U V} a ↦ by
         ext x
         exact congrFun (hn U V a x) i }⟩
  let c := Fan.mk M π
  have hc : IsLimit c := by
    refine Fan.IsLimit.mk _ (fun s ↦ ?_) ?_ ?_
    · refine ⟨{ app := fun U ↦ ModuleCat.ofHom ?_
                naturality := ?_ }⟩
      · exact
          { toFun := fun x ↦ (e _).symm (fun i ↦ (s.proj i).val.app _ x)
            map_add' := by
              intro x y
              apply (e _).injective
              simp only [AddEquiv.apply_symm_apply, map_add]
              rfl
            map_smul' := by
              intro a x
              apply (e _).injective
              rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
              ext i
              exact ((s.proj i).val.app _).hom.map_smul a x }
      · intro U V a
        ext x
        apply (e V).injective
        change (e V) ((e V).symm
          (fun i ↦ (s.proj i).val.app V (s.pt.val.map a x))) =
          (e V) (M.val.map a ((e U).symm (fun i ↦ (s.proj i).val.app U x)))
        rw [hn, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
        ext i
        exact PresheafOfModules.naturality_apply (s.proj i).val a x
    · intro s i
      ext U x
      exact congrFun ((e U).apply_symm_apply (fun i ↦ (s.proj i).val.app U x)) i
    · intro s m hm
      ext U x
      apply (e U).injective
      change (e U) (m.val.app U x) =
        (e U) ((e U).symm (fun i ↦ (s.proj i).val.app U x))
      rw [AddEquiv.apply_symm_apply]
      ext i
      exact congrArg (fun f ↦ f.val.app U x) (hm i)
  exact ⟨hc.conePointUniqueUpToIso (limit.isLimit _)⟩

private theorem continuousFunctions_isFree
    (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [TotallyDisconnectedSpace A]
    (N : Type v) [AddCommGroup N] [Module A N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [ContinuousSMul A N]
    (Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X))
    (p : ContinuousFunctionPresentation X A N Q) (r : ℕ)
    (d : ∀ U : X.ProEt, (Fin r → C(U.left, A)) ≃ₗ[C(U.left, A)] C(U.left, N))
    (hd : ∀ (U V : X.ProEt) (a : V ⟶ U) (x : Fin r → C(U.left, A)),
      d V (fun i ↦ (x i).comp a.left.base.hom) = (d U x).comp a.left.base.hom) :
    Mod.IsFree (condensedRingObj (Profinite.continuousMapRingObj A) X) Q := by
  let F := continuousRingModuleEquivalence X A
  let M := F.functor.obj Q
  let e (U : X.ProEtᵒᵖ) : M.val.obj U ≃+ (Fin r → ULift.{u + 1} C(U.unop.left, A)) :=
    (p.sections U.unop).trans ((d U.unop).symm.toAddEquiv.trans
      (AddEquiv.piCongrRight (fun _ ↦ AddEquiv.ulift.symm)))
  have he (U : X.ProEtᵒᵖ) (a : ULift.{u + 1} C(U.unop.left, A)) (x : M.val.obj U) :
      e U (a • x) = a • e U x := by
    change (fun i ↦ ULift.up ((d U.unop).symm (p.sections U.unop (a • x)) i)) = _
    rw [p.smul, map_smul]
    rfl
  have hn (U V : X.ProEtᵒᵖ) (a : U ⟶ V) (x : M.val.obj U) :
      e V (M.val.map a x) = fun i ↦ (continuousMapRingSheaf X A).obj.map a (e U x i) := by
    have h := hd U.unop V.unop a.unop ((d U.unop).symm (p.sections U.unop x))
    rw [LinearEquiv.apply_symm_apply] at h
    have h' := congrArg (d V.unop).symm h
    rw [LinearEquiv.symm_apply_apply, ← p.restrict] at h'
    exact congrArg (fun y ↦ fun i ↦ ULift.up (y i)) h'.symm
  obtain ⟨b⟩ := module_iso_product (continuousMapRingSheaf X A) M r e he hn
  let : HasFiniteBiproducts (SheafOfModules.{u + 1} (continuousMapRingSheaf X A)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let : PreservesBiproduct (fun _ : Fin r ↦ Mod.regular
      (condensedRingObj (Profinite.continuousMapRingObj A) X)) F.functor :=
    preservesBiproduct_of_preservesCoproduct F.functor
  let c : F.functor.obj
      (Mod.finiteFree (condensedRingObj (Profinite.continuousMapRingObj A) X) r) ≅
        ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit (continuousMapRingSheaf X A)) :=
    F.functor.mapBiproduct (fun _ : Fin r ↦ Mod.regular
      (condensedRingObj (Profinite.continuousMapRingObj A) X)) ≪≫
      biproduct.mapIso (fun _ : Fin r ↦ continuousRingRegularIso X A) ≪≫
        biproduct.isoProduct (fun _ : Fin r ↦ SheafOfModules.unit (continuousMapRingSheaf X A))
  exact ⟨r, ⟨F.fullyFaithfulFunctor.preimageIso (b ≪≫ c.symm)⟩⟩

/-- A module presented by continuous functions into a finite sum of full lattices is free.
Source: the continuous lattice sum theorem and the continuous coefficient encoding.
(blueprint: lem-sfb-continuous-lattice-sum-internal-free)

Proof. The continuous lattice sum theorem gives natural integral coordinates on
all pro-etale objects. Compose these coordinates with the supplied section
presentation. They identify the encoded module with the finite product of the
unit module sheaf. The encoding takes the finite biproduct of regular internal
modules to this same product. Full faithfulness transports the isomorphism back.
This includes rank zero, an empty base, and arbitrary finite nonempty sheet sets. -/
theorem continuousLatticeSum_isFree
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [TotallyDisconnectedSpace E] (X : Scheme.{u}) (r : ℕ)
    (J : Type w) [Finite J] [Nonempty J]
    (L : J → Submodule (continuousIntegers l E) (Fin r → E))
    (hL : ∀ j, ∃ b : Module.Basis (Fin r) (continuousIntegers l E) (L j),
      ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i)
    (Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) X))
    (p : ContinuousFunctionPresentation X (continuousIntegers l E) ↥(⨆ j, L j) Q) :
    Mod.IsFree (condensedRingObj (integralCoeff l E) X) Q := by
  let : Fintype J := Fintype.ofFinite J
  have hd : ∀ (L : J → Submodule (continuousIntegers l E) (Fin r → E)),
      (∀ j, ∃ b : Module.Basis (Fin r) (continuousIntegers l E) (L j),
        ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i) →
      ∃ d : ∀ U : X.ProEt,
          (Fin r → C(U.left, continuousIntegers l E)) ≃ₗ[
            C(U.left, continuousIntegers l E)] C(U.left, ↥(⨆ j, L j)),
        ∀ (U V : X.ProEt) (a : V ⟶ U) (x : Fin r → C(U.left, continuousIntegers l E)),
          d V (fun i ↦ (x i).comp a.left.base.hom) = (d U x).comp a.left.base.hom := by
    rw [continuousIntegers_eq l E]
    intro L hL
    exact ((continuous_lattice_sum.{u, 0, w, u} l E r J L hL).2.2 X).2.2.2.1
  obtain ⟨d, hd⟩ := hd L hL
  exact continuousFunctions_isFree X _ _ Q p r d hd

end AlgebraicGeometry.ProEtale.CondensedRing
