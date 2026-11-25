/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulDualComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Evaluation of derived maps from the Koszul complex

Source: Stacks Project, Tag 0BQZ, the finite free Koszul computation.
(blueprint: lem-sc-koszul-derived-dual-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

private theorem kprojective_Q_map_surjective
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (E T : CochainComplex (ModuleCat.{u} A) ℤ) [CochainComplex.IsKProjective E] :
    Function.Surjective (DerivedCategory.Q.map : (E ⟶ T) → _) := by
  intro v
  let a := (DerivedCategory.quotientCompQhIso (ModuleCat A)).app E
  let b := (DerivedCategory.quotientCompQhIso (ModuleCat A)).app T
  obtain ⟨h, hh⟩ := (CochainComplex.IsKProjective.Qh_map_bijective E
    ((HomotopyCategory.quotient _ _).obj T)).surjective (a.hom ≫ v ≫ b.inv)
  obtain ⟨z, hz⟩ := (HomotopyCategory.quotient _ _).map_surjective h
  refine ⟨z, ?_⟩
  apply (cancel_epi a.hom).mp
  have he := DerivedCategory.quotientCompQhIso_hom_naturality z
  simpa [a, b, hz, hh] using he.symm

private theorem Q_map_zero_iff_homotopy
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    {E T : CochainComplex (ModuleCat.{u} A) ℤ} [CochainComplex.IsKProjective E]
    (z : E ⟶ T) : DerivedCategory.Q.map z = 0 ↔ Nonempty (Homotopy z 0) := by
  constructor
  · intro hz
    rw [← HomotopyCategory.quotient_map_eq_zero_iff]
    apply (CochainComplex.IsKProjective.Qh_map_bijective E
      ((HomotopyCategory.quotient _ _).obj T)).injective
    have he := DerivedCategory.quotientCompQhIso_hom_naturality z
    rw [hz, CategoryTheory.Limits.comp_zero] at he
    exact (cancel_mono ((DerivedCategory.quotientCompQhIso (ModuleCat A)).hom.app T)).mp
      (by simpa using he)
  · rintro ⟨h⟩
    simpa using DerivedCategory.Q_map_eq_of_homotopy (ModuleCat A) h

open CochainComplex HomComplex in
private theorem Q_map_homOf_zero_iff
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    {E T : CochainComplex (ModuleCat.{u} A) ℤ} [CochainComplex.IsKProjective E]
    (c : Cocycle E T 0) :
    DerivedCategory.Q.map (Cocycle.homOf c) = 0 ↔ c ∈ coboundaries E T 0 := by
  rw [Q_map_zero_iff_homotopy A, mem_coboundaries_iff c (-1) rfl]
  constructor
  · rintro ⟨h⟩
    obtain ⟨β, hβ⟩ := (Cochain.equivHomotopy (Cocycle.homOf c) 0) h
    refine ⟨β, ?_⟩
    simpa [Cocycle.cochain_ofHom_homOf_eq_coe] using hβ.symm
  · rintro ⟨β, hβ⟩
    refine ⟨(Cochain.equivHomotopy (Cocycle.homOf c) 0).symm ⟨β, ?_⟩⟩
    simpa [Cocycle.cochain_ofHom_homOf_eq_coe] using hβ.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open CochainComplex HomComplex in
/-- Signed-dual homology computes maps out of the Koszul complex, with the
actual component evaluation on representatives. This requires neither an
augmentation nor Koszul regularity.
Source: Stacks Project, Tag 0BQZ, finite free Koszul computation, and Mathlib's
K-projective Hom-complex comparison.
(blueprint: lem-sc-koszul-derived-dual-evaluation).

Proof: The exterior basis makes every Koszul term projective, so the extension
E is K-projective by CochainComplex's natural-number extension instance. Maps
from E in the derived category are homotopy classes of complex maps, by
IsKProjective.Qh_map_bijective. Evaluate a map z to single(A,-r) in degree -r,
transporting by extendXIso.inv and singleObjXSelf.hom. The chain-map equation
identifies its evaluation with an element of the kernel of the signed dual
outgoing differential: that differential is a unit sign times precomposition
with d_(r+1,r). Conversely every such kernel element a gives a unique map z,
by mkHomToSingle applied to extendXIso.hom followed by a. A null homotopy of z
has in degree -r the equation a=d_(r,r-1) followed by its degree (-r+1,-r)
component, since the target differential vanishes. For r>0 this is precisely
membership in the incoming dual image: absorb the unit sign (-1)^r into
the homotopy component. Conversely an incoming-image element defines a null
homotopy with this component, all other components zero. For r=0 the source
term in degree 1 is zero, hence a null homotopy forces a=0, and the incoming
natural-number differential is zero. Alternatively these same equations are
Cocycle.toSingleMk_mem_coboundaries_iff and Cochain.delta_toSingleMk. Thus
evaluation induces a bijection from homotopy classes to the kernel/image
quotient. moduleCatCyclesIso and moduleCatHomologyIso identify this quotient
with abstract signed-dual homology. All maps are additive and A-linear;
Qh preserves scalars, so composing with its inverse gives e. If y has the
specified evaluation, the quotient projection equation forces
e(Q.map z)=homologyPi(y). No choice of y matters because iCycles is injective.
For r=0 this is ordinary Hom evaluation; for the zero ring all modules vanish.
This argument uses no ideal, augmentation or regularity hypothesis, because
E itself is K-projective for every f. -/
theorem exists_koszul_derived_dual_evaluation
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (r : ℕ) (f : Fin r → A) :
    ∃ e : (DerivedCategory.Q.obj
        ((koszulComplex A r f).extend ComplexShape.embeddingDownNat) ⟶
          DerivedCategory.Q.obj
            ((CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj
              (ModuleCat.of A A))) ≃ₗ[A] (koszulDualComplex A r f).homology r,
      ∀ z : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
          (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj
            (ModuleCat.of A A),
        ∀ y : (koszulDualComplex A r f).cycles r,
          (koszulDualComplex A r f).iCycles r y =
            ((koszulComplex A r f).extendXIso
              ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ z.f (-(r : ℤ)) ≫
                (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
                  (ModuleCat.of A A)).hom →
          e (DerivedCategory.Q.map z) = (koszulDualComplex A r f).homologyπ r y := by
  classical
  let K := koszulComplex A r f
  let E := K.extend ComplexShape.embeddingDownNat
  let T := (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A)
  let S := (koszulDualComplex A r f).sc r
  have (n : ℕ) : Projective (K.X n) :=
    ModuleCat.projective_of_free
      ((Finsupp.basisSingleOne : Module.Basis (Fin r) A (Fin r →₀ A)).exteriorPower n)
  have : CochainComplex.IsKProjective E := inferInstance
  let er : E.X (-(r : ℤ)) ≅ K.X r :=
    K.extendXIso ComplexShape.embeddingDownNat (i := r) (i' := -(r : ℤ)) (by simp)
  have hc (x : LinearMap.ker S.g.hom) : K.d (r + 1) r ≫ x.val = 0 := by
    have hx := LinearMap.mem_ker.mp x.property
    change (koszulDualComplex A r f).d r ((ComplexShape.up ℕ).next r) x.val = 0 at hx
    rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel r (r + 1) from rfl)] at hx
    have hx' : (-1 : A) ^ (r + 1) • (K.d (r + 1) r ≫ x.val) = 0 := by
      simpa [koszulDualComplex, koszulDualBoundary, Linear.leftComp] using hx
    exact ((isUnit_neg_one).pow (r + 1)).smul_eq_zero.mp hx'
  let C (x : LinearMap.ker S.g.hom) : Cocycle E T 0 :=
    Cocycle.toSingleMk
      (er.hom ≫ x.val)
      (by simp) (-(r : ℤ) - 1) (by omega) (by
        erw [HomologicalComplex.extend_d_eq K ComplexShape.embeddingDownNat
          (i := r + 1) (j := r) (i' := -(r : ℤ) - 1) (j' := -(r : ℤ))
          (by simp; omega) (by simp)]
        simp [er, Category.assoc, hc x])
  let F : LinearMap.ker S.g.hom →ₗ[A] (DerivedCategory.Q.obj E ⟶
      DerivedCategory.Q.obj T) :=
    { toFun := fun x ↦ DerivedCategory.Q.map (Cocycle.homOf (C x))
      map_add' := by
        intro x y
        rw [← Functor.map_add]
        congr 1
        apply HomologicalComplex.to_single_hom_ext
        simp only [HomologicalComplex.add_f_apply, C, Cocycle.homOf_f,
          Cocycle.toSingleMk_coe, Cochain.toSingleMk_v]
        simp [S, koszulDualComplex, Category.assoc]
      map_smul' := by
        intro a x
        rw [← Functor.map_smul]
        congr 1
        apply HomologicalComplex.to_single_hom_ext
        simp only [RingHom.id_apply, HomologicalComplex.smul_f_apply, C,
          Cocycle.homOf_f, Cocycle.toSingleMk_coe, Cochain.toSingleMk_v]
        simp [S, koszulDualComplex, Category.assoc] }
  have hsurj : Function.Surjective F := by
    intro v
    obtain ⟨z, rfl⟩ := kprojective_Q_map_surjective A E T v
    obtain ⟨a, ha, heq⟩ := Cocycle.toSingleMk_surjective (Cocycle.ofHom z)
      (-(r : ℤ)) (by simp) (-(r : ℤ) - 1) (by omega)
    let x : LinearMap.ker S.g.hom :=
      ⟨er.inv ≫ a, by
        change S.g _ = 0
        change (koszulDualComplex A r f).d r ((ComplexShape.up ℕ).next r) _ = 0
        rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel r (r + 1)
          from rfl)]
        have he : K.d (r + 1) r ≫ er.inv ≫ a = 0 := by
          erw [HomologicalComplex.extend_d_eq K ComplexShape.embeddingDownNat
            (i := r + 1) (j := r) (i' := -(r : ℤ) - 1) (j' := -(r : ℤ))
            (by simp; omega) (by simp)] at ha
          exact (cancel_epi (K.extendXIso ComplexShape.embeddingDownNat
            (i := r + 1) (i' := -(r : ℤ) - 1) (by simp; omega)).hom).mp
              (by simpa [er, Category.assoc] using ha)
        simpa [S, koszulDualComplex, koszulDualBoundary, Linear.leftComp,
          Category.assoc, he]⟩
    have hx : C x = Cocycle.ofHom z := by
      simpa [C, x, Category.assoc] using heq
    refine ⟨x, ?_⟩
    change DerivedCategory.Q.map (Cocycle.homOf (C x)) = _
    rw [hx, Cocycle.homOf_ofHom_eq_self]
  have hker : LinearMap.ker F = LinearMap.range S.moduleCatToCycles := by
    ext x
    change DerivedCategory.Q.map (Cocycle.homOf (C x)) = 0 ↔
      ∃ y, S.moduleCatToCycles y = x
    rw [Q_map_homOf_zero_iff A]
    dsimp only [C]
    rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ (-(r : ℤ) + 1) (by omega)]
    cases r with
    | zero =>
      have hf0 : S.f = 0 := by
        change (koszulDualComplex A 0 f).d ((ComplexShape.up ℕ).prev 0) 0 = 0
        exact (koszulDualComplex A 0 f).shape _ _ (by simp [ComplexShape.up_Rel])
      have hb0 : S.moduleCatToCycles = 0 := by
        ext y
        change S.f y = 0
        rw [hf0]
        rfl
      rw [hb0]
      constructor
      · rintro ⟨g, hg⟩
        have hgz : g = 0 := (CochainComplex.isZero_of_isStrictlyLE E 0 1).eq_of_src _ _
        rw [hgz, Limits.comp_zero] at hg
        have hx : x = 0 := by
          apply Subtype.ext
          simpa [er] using hg.symm
        exact ⟨0, by simp [hx]⟩
      · rintro ⟨y, hy⟩
        rw [← hy]
        exact ⟨0, by simp⟩
    | succ p =>
      have hp : (ComplexShape.up ℕ).prev (p + 1) = p :=
        (ComplexShape.up ℕ).prev_eq' rfl
      simp only [Subtype.ext_iff]
      change (∃ g : E.X (-(↑(p + 1) : ℤ) + 1) ⟶ ModuleCat.of A A,
        E.d (-(↑(p + 1) : ℤ)) (-(↑(p + 1) : ℤ) + 1) ≫ g =
          er.hom ≫ x.val) ↔
        ∃ y : (koszulDualComplex A (p + 1) f).X ((ComplexShape.up ℕ).prev (p + 1)),
          (koszulDualComplex A (p + 1) f).d ((ComplexShape.up ℕ).prev (p + 1))
            (p + 1) y = x.val
      rw [hp]
      let ep := K.extendXIso ComplexShape.embeddingDownNat (i := p)
        (i' := -(↑(p + 1) : ℤ) + 1) (by simp)
      constructor
      · rintro ⟨g, hg⟩
        have he : K.d (p + 1) p ≫ ep.inv ≫ g = x.val := by
          erw [HomologicalComplex.extend_d_eq K ComplexShape.embeddingDownNat
            (i := p + 1) (j := p) (i' := -(↑(p + 1) : ℤ))
            (j' := -(↑(p + 1) : ℤ) + 1) (by simp) (by simp)] at hg
          exact (cancel_epi er.hom).mp (by simpa [ep, er, Category.assoc] using hg)
        refine ⟨(-1 : A) ^ (p + 1) • (ep.inv ≫ g), ?_⟩
        have hh : (-1 : A) ^ (p + 1) •
            (K.d (p + 1) p ≫ ((-1 : A) ^ (p + 1) • (ep.inv ≫ g))) = x.val := by
          rw [Linear.comp_smul, smul_smul, ← mul_pow, neg_one_mul, neg_neg,
            one_pow, one_smul, he]
        simpa [koszulDualComplex, koszulDualBoundary, Linear.leftComp] using hh
      · rintro ⟨y, hy⟩
        refine ⟨ep.hom ≫ ((-1 : A) ^ (p + 1) • y), ?_⟩
        erw [HomologicalComplex.extend_d_eq K ComplexShape.embeddingDownNat
          (i := p + 1) (j := p) (i' := -(↑(p + 1) : ℤ))
            (j' := -(↑(p + 1) : ℤ) + 1) (by simp) (by simp)]
        have he : K.d (p + 1) p ≫ ((-1 : A) ^ (p + 1) • y) = x.val := by
          have hh : (-1 : A) ^ (p + 1) • (K.d (p + 1) p ≫ y) = x.val := by
            simpa [koszulDualComplex, koszulDualBoundary, Linear.leftComp] using hy
          exact (Linear.comp_smul _ _ _ (K.d (p + 1) p) ((-1 : A) ^ (p + 1))
            (y : K.X p ⟶ ModuleCat.of A A)).trans hh
        simpa [ep, er, Category.assoc] using congrArg
          (fun a ↦ er.hom ≫ a) he
  let q := F.quotKerEquivOfSurjective hsurj
  let H := S.moduleCatHomologyIso.toLinearEquiv
  let d := H.trans ((Submodule.quotEquivOfEq _ _ hker).symm.trans q)
  refine ⟨d.symm, ?_⟩
  intro z y hy
  let x := S.moduleCatCyclesIso.hom y
  have hxval : (x.val : K.X r ⟶ ModuleCat.of A A) =
      er.inv ≫ z.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom := by
    have hi := S.moduleCatCyclesIso_hom_i_apply y
    change x.val = (koszulDualComplex A r f).iCycles r y at hi
    exact hi.trans hy
  have hcz : Cocycle.homOf (C x) = z := by
    apply HomologicalComplex.to_single_hom_ext
    simp only [C, Cocycle.homOf_f, Cocycle.toSingleMk_coe, Cochain.toSingleMk_v]
    rw [hxval]
    simp [Category.assoc]
  have hH : H (S.homologyπ y) = Submodule.Quotient.mk x := by
    exact S.π_moduleCatCyclesIso_hom_apply y
  apply d.injective
  erw [d.apply_symm_apply]
  change DerivedCategory.Q.map z = d (S.homologyπ y)
  change DerivedCategory.Q.map z =
    q ((Submodule.quotEquivOfEq _ _ hker).symm (H (S.homologyπ y)))
  rw [hH]
  have hq : (Submodule.quotEquivOfEq _ _ hker).symm (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
    apply (Submodule.quotEquivOfEq _ _ hker).injective
    simp
  erw [hq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  change DerivedCategory.Q.map z = DerivedCategory.Q.map (Cocycle.homOf (C x))
  rw [hcz]

end ExteriorAlgebra
