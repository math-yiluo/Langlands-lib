/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberSystem
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # The ring colimit of the middle closed fibres

Source: Stacks Project, Algebra, Tag 00R7, quotient systems before the second use of 00R6.
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-ring-colimit)

The limit map is explicitly descended to each quotient. The union of the images of
stage ideals is an ideal, since directedness lets any two representatives move to
one stage. It contains every image of a coefficient in the maximal ideal of R:
lift that coefficient along rlimit_surj; a unit lift would have a unit image.
Thus every element of the extended maximal ideal comes from a stage ideal.
Using slimit_eq after moving representatives to a common stage proves eventual
equality in the quotients. Together with slimit_surj this identifies the cocone
as a colimit. Its unique comparison with the categorical colimit constructs fiberAEquiv.
-/

@[expose] public section

universe z u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module.NoetherianLocalModelTower

section IdealUnion

variable {I : Type z} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (A : I → Type u) [∀ i, CommRing (A i)]
  (f : ∀ i j, i ≤ j → A i →+* A j)
  (L : Type v) [CommRing L] (π : ∀ i, A i →+* L)
  (hπ : ∀ i j h, (π j).comp (f i j h) = π i)
  (hrep : ∀ x : L, ∃ i a, π i a = x)
  (J : ∀ i, Ideal (A i))
  (hJ : ∀ i j h, J i ≤ (J j).comap (f i j h))

/-- The union of images of compatible ideals in a directed ring system. -/
private def idealUnion : Ideal L where
  carrier := {x | ∃ i a, a ∈ J i ∧ π i a = x}
  zero_mem' := ⟨Classical.arbitrary I, 0, (J _).zero_mem, map_zero _⟩
  add_mem' := by
    rintro x y ⟨i, a, ha, rfl⟩ ⟨j, b, hb, rfl⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, f i k hik a + f j k hjk b,
      (J k).add_mem (hJ i k hik ha) (hJ j k hjk hb), ?_⟩
    rw [map_add]
    exact congrArg₂ (· + ·) (RingHom.congr_fun (hπ i k hik) a)
      (RingHom.congr_fun (hπ j k hjk) b)
  smul_mem' := by
    rintro r x ⟨i, a, ha, rfl⟩
    obtain ⟨j, b, rfl⟩ := hrep r
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, f j k hjk b * f i k hik a,
      (J k).mul_mem_left _ (hJ i k hik ha), ?_⟩
    rw [map_mul]
    exact congrArg₂ (· * ·) (RingHom.congr_fun (hπ j k hjk) b)
      (RingHom.congr_fun (hπ i k hik) a)

end IdealUnion

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
  [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [AddCommGroup M]
  [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
  (X : Module.NoetherianLocalModelTower R S S' M)

attribute [local instance] Module.NoetherianLocalModelTower.preorder
  Module.NoetherianLocalModelTower.nonempty Module.NoetherianLocalModelTower.directed
  Module.NoetherianLocalModelTower.commR Module.NoetherianLocalModelTower.commS
  Module.NoetherianLocalModelTower.commT Module.NoetherianLocalModelTower.localR
  Module.NoetherianLocalModelTower.algRS Module.NoetherianLocalModelTower.algST
  Module.NoetherianLocalModelTower.algRT Module.NoetherianLocalModelTower.towerRST
  Module.NoetherianLocalModelTower.algRLimit Module.NoetherianLocalModelTower.algSLimit

omit [IsLocalRing R] in
/-- The middle stage ideals are compatible with transitions. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-ring-colimit)
-/
theorem fiberIdealS_transition (i j : X.ι) (h : i ≤ j) :
    X.fiberIdealS i ≤ (X.fiberIdealS j).comap (X.smap i j h) := by
  let := X.rmap_local i j h
  exact Ideal.map_le_iff_le_comap.mp
    (map_fiberIdeal_le (X.rmap i j h) (X.smap i j h) _ _ (X.rs_comm i j h))

/-- The middle stage ideals map into the closed-fibre ideal in the limit ring. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-ring-colimit)
-/
theorem fiberIdealS_limit (i : X.ι) :
    X.fiberIdealS i ≤
      (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)).comap
        (algebraMap (X.S₀ i) S) := by
  let := X.rlimit_local i
  exact Ideal.map_le_iff_le_comap.mp
    (map_fiberIdeal_le (algebraMap (X.R₀ i) R) (algebraMap (X.S₀ i) S)
      _ _ (X.rs_limit_comm i))

/-- Every element of the limit closed-fibre ideal comes from a stage ideal. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-ring-colimit)
-/
theorem fiberIdealS_limit_rep (s : S)
    (hs : s ∈ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) :
    ∃ i a, a ∈ X.fiberIdealS i ∧ algebraMap (X.S₀ i) S a = s := by
  let J := idealUnion X.S₀ X.smap S (fun i ↦ algebraMap (X.S₀ i) S)
    X.slimit_comm X.slimit_surj X.fiberIdealS X.fiberIdealS_transition
  have hJ : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    obtain ⟨i, a, ha⟩ := X.rlimit_surj r
    have hai : a ∈ IsLocalRing.maximalIdeal (X.R₀ i) := by
      intro hua
      exact hr (ha ▸ (algebraMap (X.R₀ i) R).isUnit_map hua)
    refine ⟨i, algebraMap (X.R₀ i) (X.S₀ i) a, Ideal.mem_map_of_mem _ hai, ?_⟩
    exact (RingHom.congr_fun (X.rs_limit_comm i) a).trans (congrArg (algebraMap R S) ha)
  exact hJ hs

/-- A middle quotient representative killed in the limit is killed at a later stage. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-ring-colimit)
-/
theorem fiberS_eventual_zero (i : X.ι) (a : X.S₀ i)
    (ha : algebraMap (X.S₀ i) S a ∈
      Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) :
    ∃ j h, X.smap i j h a ∈ X.fiberIdealS j := by
  obtain ⟨j, b, hb, he⟩ := X.fiberIdealS_limit_rep _ ha
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hk : algebraMap (X.S₀ k) S (X.smap i k hik a) =
      algebraMap (X.S₀ k) S (X.smap j k hjk b) := by
    exact (RingHom.congr_fun (X.slimit_comm i k hik) a).trans
      (he.symm.trans (RingHom.congr_fun (X.slimit_comm j k hjk) b).symm)
  obtain ⟨l, hkl, hl⟩ := X.slimit_eq k _ _ hk
  refine ⟨l, hik.trans hkl, ?_⟩
  have hmem := X.fiberIdealS_transition k l hkl (X.fiberIdealS_transition j k hjk hb)
  change X.smap k l hkl (X.smap j k hjk b) ∈ X.fiberIdealS l at hmem
  rw [← hl] at hmem
  simpa only [X.sSystem.map_map] using hmem

/-- The middle closed fibre of the limit. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-ring-colimit)
-/
abbrev FiberLimitS :=
  S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)

/-- The stage quotient map to the limit quotient. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-ring-colimit)
-/
def fiberSLimit (i : X.ι) : X.FiberS i →+* FiberLimitS (R := R) (S := S) :=
  Ideal.quotientMap _ (algebraMap (X.S₀ i) S) (X.fiberIdealS_limit i)

/-- The ring cocone of the middle closed fibres. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-ring-colimit)
-/
def fiberSCocone : Cocone X.fiberA where
  pt := CommRingCat.of (ULift.{max u v w} (FiberLimitS (R := R) (S := S)))
  ι := {
    app := fun i ↦ CommRingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp (X.fiberSLimit i))
    naturality := by
      intro i j f
      apply CommRingCat.hom_ext
      apply Ideal.Quotient.ringHom_ext
      ext a
      change ULift.up (Ideal.Quotient.mk _
        (algebraMap (X.S₀ j) S (X.smap i j (leOfHom f) a))) =
        ULift.up (Ideal.Quotient.mk _ (algebraMap (X.S₀ i) S a))
      exact congrArg (fun s ↦ ULift.up (Ideal.Quotient.mk _ s))
        (RingHom.congr_fun (X.slimit_comm i j (leOfHom f)) a) }

/-- The middle closed-fibre cocone is a colimit. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-ring-colimit)
-/
noncomputable def fiberSCoconeIsColimit : IsColimit X.fiberSCocone := by
  letI := reflectsColimit_of_reflectsIsomorphisms X.fiberA (forget CommRingCat)
  apply isColimitOfReflects (forget CommRingCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective x.down
    obtain ⟨i, a, ha⟩ := X.slimit_surj s
    refine ⟨i, Ideal.Quotient.mk _ a, ?_⟩
    change x = ULift.up (Ideal.Quotient.mk _ (algebraMap (X.S₀ i) S a))
    rw [ha, hs]
    rfl
  · intro i x y h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hab : algebraMap (X.S₀ i) S (a - b) ∈
        Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, map_sub, sub_eq_zero]
      exact congrArg ULift.down h
    obtain ⟨j, hij, hj⟩ := X.fiberS_eventual_zero i (a - b) hab
    refine ⟨j, homOfLE hij, ?_⟩
    change Ideal.Quotient.mk _ (X.smap i j hij a) =
      Ideal.Quotient.mk _ (X.smap i j hij b)
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← map_sub]
    exact hj

/-- The categorical middle closed-fibre colimit is the limit quotient. 
(blueprint: def-weil-pbc-noetherian-local-model-tower-fiber-ring-colimit)
-/
noncomputable def fiberAEquiv :
    (colimit X.fiberA : CommRingCat.{max u v w}) ≃+* FiberLimitS (R := R) (S := S) :=
  ((colimit.isColimit X.fiberA).coconePointUniqueUpToIso
    X.fiberSCoconeIsColimit).commRingCatIsoToRingEquiv.trans ULift.ringEquiv

end Module.NoetherianLocalModelTower
