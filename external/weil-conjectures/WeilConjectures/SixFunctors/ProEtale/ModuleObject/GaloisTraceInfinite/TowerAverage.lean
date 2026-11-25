/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerContinuity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerDerived

/-!
# The trace projector of a Galois tower is the average of the Galois action

Let `T` be a Galois tower over `X` (`AlgebraicGeometry.ProEtale.GaloisTower`) with Galois groups
of order invertible in `Λ`. The projector `τ ≫ η` on `g_{∞*} g_∞^* M`, made of the normalized trace
`τ` and the unit `η`, is, restricted to the finite level `j`, the average over `Γ_j` of the unit
transports along lifts to `Y_∞` of the elements of `Γ_j`. Consequently every Galois-coinvariant
map out of a colimit-preserving additive image of the levelwise complex `g_{∞*} g_∞^* K` is fixed
by the projector: the projector is the projector onto the invariants.

## Main results

* `AlgebraicGeometry.ProEtale.GaloisTower.card_nsmul_infTransport_comp_trace_comp_infUnit`: the
  projector `τ ≫ η` at the level `j` is the average of the Galois action.
* `GaloisTower.sum_const_complexCocone_ι_app_comp_complexTrace_comp_unit`:
  the same for complexes (with `|Γ_j| • x` written as the sum of a constant family).
* `AlgebraicGeometry.ProEtale.GaloisTower.map_complexTrace_comp_unit_comp_eq_of_invariant`:
  Galois-coinvariant maps out of the continuous image of the levelwise model are fixed by the
  trace projector.
-/

@[expose] public section

-- several lemmas do not need all the instances of the section variables
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (hd : ∀ (j : T.J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      IsIso (Fintype.card (T.Γ j) • 𝟙 N))

/-! ### Module objects -/

section Module

variable (M : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- `|Γ_j|` times the normalized trace at the level `j` is the trace. -/
lemma card_nsmul_normTrace (j : T.J) :
    Fintype.card (T.Γ j) • T.normTrace Λ M hd j = (T.levelTrace Λ j).app M := by
  have := hd j M
  have h : Fintype.card (T.Γ j) • inv (Fintype.card (T.Γ j) • 𝟙 M) = 𝟙 M :=
    calc _ = inv (Fintype.card (T.Γ j) • 𝟙 M) ≫ (Fintype.card (T.Γ j) • 𝟙 M) := by
          rw [Preadditive.comp_nsmul, comp_id]
      _ = 𝟙 M := IsIso.inv_hom_id _
  rw [normTrace, normalizedTrace, ← Preadditive.comp_nsmul, h, comp_id]

/-- **The trace projector is the average of the Galois action**: restricted to the level `j`,
`|Γ_j|` times the projector `τ ≫ η` on `g_{∞*} g_∞^* M` is the sum of the unit transports along
lifts `σ a` to `Y_∞` of the elements `a ∈ Γ_j`. -/
lemma card_nsmul_infTransport_comp_trace_comp_infUnit (hc : IsColimit (T.moduleCocone Λ M))
    (j : T.J) (σ : T.Γ j → (Yinf ⟶ Yinf)) (hσ : ∀ a, σ a ≫ ginf = ginf)
    (hσj : ∀ a, σ a ≫ T.π j = T.π j ≫ T.ρ j a) :
    Fintype.card (T.Γ j) • (T.infTransport Λ M j ≫ T.trace Λ M hd hc ≫ (infUnit Λ ginf).app M) =
      ∑ a, T.infTransport Λ M j ≫ infAction Λ M (σ a) (hσ a) := by
  rw [← assoc, T.infTransport_comp_trace, ← Preadditive.nsmul_comp, T.card_nsmul_normTrace,
    ← T.levelUnit_app_comp_infTransport, ← assoc, ← NatTrans.comp_app,
    T.levelTrace_comp_levelUnit, NatTrans.app_sum, Preadditive.sum_comp]
  exact Finset.sum_congr rfl fun a _ ↦
    (T.infTransport_comp_infAction Λ M (σ a) (hσ a) j a (hσj a)).symm

section

/- We use the additive structure on morphisms of module objects coming from the preadditive
structure, which is the one obtained degreewise from complexes: this avoids comparing different
(but definitionally equal) instances in the kernel at concrete objects. -/
attribute [-instance] Mod.instAddCommGroupHom_weilConjectures

/-- `GaloisTower.card_nsmul_infTransport_comp_trace_comp_infUnit`, with the multiple `|Γ_j| • x`
written as the sum of the constant family `x` over `Γ_j`. -/
lemma sum_const_infTransport_comp_trace_comp_infUnit (hc : IsColimit (T.moduleCocone Λ M))
    (j : T.J) (σ : T.Γ j → (Yinf ⟶ Yinf)) (hσ : ∀ a, σ a ≫ ginf = ginf)
    (hσj : ∀ a, σ a ≫ T.π j = T.π j ≫ T.ρ j a) :
    ∑ _a : T.Γ j, T.infTransport Λ M j ≫ T.trace Λ M hd hc ≫ (infUnit Λ ginf).app M =
      ∑ a, T.infTransport Λ M j ≫ infAction Λ M (σ a) (hσ a) := by
  rw [Finset.sum_const, Finset.card_univ]
  exact T.card_nsmul_infTransport_comp_trace_comp_infUnit Λ hd M hc j σ hσ hσj

end

end Module
/-! ### Complexes -/

section Complex

variable (K : CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
  (hc : ∀ n, IsColimit (T.moduleCocone Λ (K.X n)))

/-- The degree `n` component of the levelwise normalized trace. -/
lemma complexTrace_f (n : ℤ) :
    (T.complexTrace Λ hd K hc).f n = T.trace Λ (K.X n) hd (hc n) := rfl

/-- The degree `n` component of the unit of `g_∞^* ⊣ g_{∞*}` on complexes. -/
lemma mapHomologicalComplex_unit_app_f_eq_infUnit (n : ℤ) :
    (((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app K).f n =
      (infUnit Λ ginf).app (K.X n) := by
  rw [Adjunction.mapHomologicalComplex_unit_app_f]
  rfl

/-- The degree `n` component of the unit transport on complexes. -/
lemma mapHomologicalComplex_unitTransport_app_f (σ : Yinf ⟶ Yinf) (hσ : σ ≫ ginf = ginf)
    (n : ℤ) :
    ((NatTrans.mapHomologicalComplex (unitTransport Λ σ hσ hσ) _).app K).f n =
      infAction Λ (K.X n) σ hσ := by
  rw [infAction_eq]
  rfl

/-- The degree `n` component of the trace projector on the image of the level `j`. -/
lemma complexCocone_ι_app_f_comp_complexTrace_f_comp_unit_app_f (j : T.J) (n : ℤ) :
    ((T.complexCocone Λ K).ι.app j).f n ≫ (T.complexTrace Λ hd K hc).f n ≫
      (((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app K).f n
    = T.infTransport Λ (K.X n) j ≫ T.trace Λ (K.X n) hd (hc n) ≫ (infUnit Λ ginf).app (K.X n) := by
  rw [complexCocone_ι_app_f, complexTrace_f, mapHomologicalComplex_unit_app_f_eq_infUnit]

/-- The degree `n` component of the unit transport on the image of the level `j`. -/
lemma complexCocone_ι_app_f_comp_unitTransport_app_f (j : T.J) (σ : Yinf ⟶ Yinf)
    (hσ : σ ≫ ginf = ginf) (n : ℤ) :
    ((T.complexCocone Λ K).ι.app j).f n ≫
      ((NatTrans.mapHomologicalComplex (unitTransport Λ σ hσ hσ) _).app K).f n =
    T.infTransport Λ (K.X n) j ≫ infAction Λ (K.X n) σ hσ := by
  rw [complexCocone_ι_app_f, mapHomologicalComplex_unitTransport_app_f]

section

/- We use the additive structures on morphisms of complexes and of module objects coming from
the preadditive structures: this avoids comparing different (but definitionally equal) instances
in the kernel at concrete objects. -/
attribute [-instance] HomologicalComplex.instAddCommGroupHom
  Mod.instAddCommGroupHom_weilConjectures

/-- **The trace projector of a complex is the average of the Galois action**: restricted to the
level `j`, the sum over `Γ_j` of the projector on `g_{∞*} g_∞^* K` (that is, `|Γ_j|` times the
projector) is the sum of the unit transports along lifts `σ a` to `Y_∞` of the elements
`a ∈ Γ_j`. -/
lemma sum_const_complexCocone_ι_app_comp_complexTrace_comp_unit (j : T.J)
    (σ : T.Γ j → (Yinf ⟶ Yinf)) (hσ : ∀ a, σ a ≫ ginf = ginf)
    (hσj : ∀ a, σ a ≫ T.π j = T.π j ≫ T.ρ j a) :
    ∑ _a : T.Γ j, (T.complexCocone Λ K).ι.app j ≫ T.complexTrace Λ hd K hc ≫
      ((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app K =
    ∑ a, (T.complexCocone Λ K).ι.app j ≫
      (NatTrans.mapHomologicalComplex (unitTransport Λ (σ a) (hσ a) (hσ a)) _).app K := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [← HomologicalComplex.eval_map, ← HomologicalComplex.eval_map, Functor.map_sum,
    Functor.map_sum]
  simp only [HomologicalComplex.eval_map, HomologicalComplex.comp_f]
  -- the identifications of the terms are done generically, with all the terms given explicitly,
  -- to avoid kernel unfolding of the concrete functors
  exact Finset.sum_const_eq_sum_of_eq
    (g := T.infTransport Λ (K.X n) j ≫ T.trace Λ (K.X n) hd (hc n) ≫ (infUnit Λ ginf).app (K.X n))
    (fun a ↦ T.infTransport Λ (K.X n) j ≫ infAction Λ (K.X n) (σ a) (hσ a)) _
    (T.complexCocone_ι_app_f_comp_complexTrace_f_comp_unit_app_f Λ hd K hc j n)
    (T.sum_const_infTransport_comp_trace_comp_infUnit Λ hd (K.X n) (hc n) j σ hσ hσj)
    fun a ↦ (T.complexCocone_ι_app_f_comp_unitTransport_app_f Λ K j (σ a) (hσ a) n).symm

end

/-- **The trace projector is the projector onto the invariants**: Galois-coinvariant maps out of
the continuous image of the levelwise model are fixed by the trace projector. Precisely, let
`F` be an additive functor out of complexes of `Λ_X`-modules which preserves the colimit
`g_{∞*} g_∞^* K = colim_j g_{j*} g_j^* K`, and `act i` automorphisms of `Y_∞` over `X` covering
every element of every finite Galois group. If multiplication by the orders `|Γ_j|` is invertible
on `W`, then every map `φ : F (g_{∞*} g_∞^* K) ⟶ W` invariant under the unit transports along the
`act i` is fixed by the image under `F` of the projector `τ ≫ η`. -/
theorem map_complexTrace_comp_unit_comp_eq_of_invariant {A : Type*} [Category A] [Preadditive A]
    (F : CochainComplex
      (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ ⥤ A)
    [F.Additive] (hF : IsColimit (F.mapCocone (T.complexCocone Λ K))) {ι : Type*}
    (act : ι → (Yinf ⟶ Yinf)) (hact : ∀ i, act i ≫ ginf = ginf)
    (hlift : ∀ j a, ∃ i, act i ≫ T.π j = T.π j ≫ T.ρ j a) {W : A}
    (hW : ∀ j, IsIso (Fintype.card (T.Γ j) • 𝟙 W)) (φ : F.obj (T.complexCocone Λ K).pt ⟶ W)
    (hφ : ∀ i, F.map ((NatTrans.mapHomologicalComplex
      (unitTransport Λ (act i) (hact i) (hact i)) _).app K) ≫ φ = φ) :
    F.map (T.complexTrace Λ hd K hc ≫
      ((CondensedRing.upperStarLowerStarAdjunction Λ ginf).mapHomologicalComplex _).unit.app K) ≫
        φ = φ := by
  refine hF.comp_eq_of_sum_const_comp_eq_sum _ (fun i ↦ F.map ((NatTrans.mapHomologicalComplex
    (unitTransport Λ (act i) (hact i) (hact i)) _).app K)) φ hφ fun j ↦ ?_
  choose σ hσ using hlift j
  refine ⟨T.Γ j, inferInstance, σ, hW j, ?_⟩
  rw [Functor.mapCocone_ι_app]
  refine F.sum_const_map_comp_map_eq_sum _ _ _ ?_
  -- we redo the proof of `GaloisTower.sum_const_complexCocone_ι_app_comp_complexTrace_comp_unit`
  -- here, to avoid comparing different (but definitionally equal) instances in the kernel
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rw [← HomologicalComplex.eval_map, ← HomologicalComplex.eval_map, Functor.map_sum,
    Functor.map_sum]
  simp only [HomologicalComplex.eval_map, HomologicalComplex.comp_f]
  exact Finset.sum_const_eq_sum_of_eq
    (g := T.infTransport Λ (K.X n) j ≫ T.trace Λ (K.X n) hd (hc n) ≫ (infUnit Λ ginf).app (K.X n))
    (fun a ↦ T.infTransport Λ (K.X n) j ≫ infAction Λ (K.X n) (act (σ a)) (hact (σ a))) _
    (T.complexCocone_ι_app_f_comp_complexTrace_f_comp_unit_app_f Λ hd K hc j n)
    (T.sum_const_infTransport_comp_trace_comp_infUnit Λ hd (K.X n) (hc n) j
      (fun a ↦ act (σ a)) (fun a ↦ hact (σ a)) hσ)
    fun a ↦ (T.complexCocone_ι_app_f_comp_unitTransport_app_f Λ K j (act (σ a)) (hact (σ a))
      n).symm

end Complex

end AlgebraicGeometry.ProEtale.GaloisTower
