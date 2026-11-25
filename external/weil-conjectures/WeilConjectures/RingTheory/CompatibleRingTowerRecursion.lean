/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Algebra.Algebra.Hom

import Mathlib.SetTheory.Cardinal.Order

/-!
# Compatible ring towers by well-founded recursion

Source: Stacks Project, Algebra, Lemma 10.159.1 (Tag 03C3), fourth proof paragraph.
(blueprint: new-compatible-ring-tower-recursion)

The private records keep all carriers in a fixed universe, together with tagged incoming
algebra maps. A local coherence predicate allows ordinary well-founded recursion to choose
compatible stages; diagonal transition maps are identities.
-/

@[expose] public section

universe u v w

namespace IsLocalRing

/-- Choose locally admissible values by recursion; induction rules out the default branch. -/
private theorem coherentChoice {I : Type w} [Preorder I] [WellFoundedLT I]
    {X : Type*} (x₀ : X)
    (C : ∀ i : I, (∀ j, j < i → X) → X → Prop)
    (hC : ∀ i p, (∀ j (hj : j < i),
      C j (fun k hk ↦ p k (lt_trans hk hj)) (p j hj)) → ∃ x, C i p x) :
    ∃ a : I → X, ∀ i, C i (fun j _ ↦ a j) (a i) := by
  classical
  let F : ∀ i : I, (∀ j, j < i → X) → X := fun i p ↦
    if h : ∃ x, C i p x then h.choose else x₀
  let a : I → X := WellFoundedLT.fix F
  refine ⟨a, ?_⟩
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have he : ∃ x, C i (fun j _ ↦ a j) x := hC i _ (fun j hj ↦ ih j hj)
    change C i (fun j _ ↦ a j) (WellFoundedLT.fix F i)
    rw [WellFoundedLT.fix_eq]
    change C i (fun j _ ↦ a j) (if h : ∃ x, C i (fun j _ ↦ a j) x then
      h.choose else x₀)
    rw [dite_eq_left he]
    exact he.choose_spec

/-- A bundled stage, with its carrier still in the specified universe. -/
private structure TowerStage (R : Type u) [CommRing R] (K : Type v) [CommRing K] where
  carrier : Type w
  ring : CommRing carrier
  alg : @Algebra R carrier _ ring.toSemiring
  ψ : @RingHom carrier K ring.toNonAssocSemiring _

/-- Recover the bundled ring structure within the private construction. -/
private instance stageRing {R : Type u} [CommRing R] {K : Type v} [CommRing K]
    (S : TowerStage.{u, v, w} R K) : CommRing S.carrier := S.ring

/-- Recover the bundled algebra structure within the private construction. -/
private instance stageAlgebra {R : Type u} [CommRing R] {K : Type v} [CommRing K]
    (S : TowerStage.{u, v, w} R K) : Algebra R S.carrier := S.alg

/-- Algebra maps between the bundled stages. -/
private abbrev TowerHom {R : Type u} [CommRing R] {K : Type v} [CommRing K]
    (S T : TowerStage.{u, v, w} R K) := S.carrier →ₐ[R] T.carrier

/-- Change only the source tag of a map along an equality of bundled stages. -/
private def castTowerHom {R : Type u} [CommRing R] {K : Type v} [CommRing K]
    {S S' T : TowerStage.{u, v, w} R K} (h : S = S') (f : TowerHom S T) :
    TowerHom S' T := h ▸ f

/-- Opposite source transports cancel by equality induction. -/
private theorem castTowerHom_cancel {R : Type u} [CommRing R]
    {K : Type v} [CommRing K] {S S' T : TowerStage.{u, v, w} R K}
    (h : S = S') (f : TowerHom S T) :
    castTowerHom h.symm (castTowerHom h f) = f := by
  cases h
  rfl

/-- One stage with an incoming map and its source tag at every index. -/
private structure TowerRecord (R : Type u) [CommRing R] (K : Type v) [CommRing K]
    (I : Type w) where
  stage : TowerStage.{u, v, w} R K
  source : I → TowerStage.{u, v, w} R K
  arrow : ∀ i, TowerHom (source i) stage

/-- Interpret an incoming map using an equality with the earlier stage. -/
private def recordMap {R : Type u} [CommRing R] {K : Type v} [CommRing K]
    {I : Type w} (s t : TowerRecord.{u, v, w} R K I) (i : I)
    (h : t.source i = s.stage) : TowerHom s.stage t.stage := castTowerHom h (t.arrow i)

/-- Local stage properties and coherence with all strict predecessors. -/
private def RecordGood {R : Type u} [CommRing R] {K : Type v} [CommRing K]
    {I : Type w} [Preorder I] (q : I → K)
    (P : ∀ (A : Type w) [CommRing A] [Algebra R A], (A →+* K) → Prop)
    (i : I) (p : ∀ j, j < i → TowerRecord.{u, v, w} R K I)
    (t : TowerRecord.{u, v, w} R K I) : Prop :=
  P t.stage.carrier t.stage.ψ ∧ (∃ a, t.stage.ψ a = q i) ∧
    ∃ hs : ∀ j (hj : j < i), t.source j = (p j hj).stage,
      (∀ j (hj : j < i) a,
        t.stage.ψ (recordMap (p j hj) t j (hs j hj) a) = (p j hj).stage.ψ a) ∧
      (∀ j k (hjk : j < k) (hk : k < i)
        (hjk' : (p k hk).source j = (p j (lt_trans hjk hk)).stage),
        (recordMap (p k hk) t k (hs k hk)).comp
          (recordMap (p j (lt_trans hjk hk)) (p k hk) j hjk') =
        recordMap (p j (lt_trans hjk hk)) t j (hs j (lt_trans hjk hk)))

/-- Use identities on the diagonal and the later record's incoming map off the diagonal. -/
private noncomputable def familyMap {R : Type u} [CommRing R] {K : Type v} [CommRing K]
    {I L : Type w} [LinearOrder I] (key : I → L)
    (a : I → TowerRecord.{u, v, w} R K L)
    (hs : ∀ i j, i < j → (a j).source (key i) = (a i).stage)
    (i j : I) (h : i ≤ j) : TowerHom (a i).stage (a j).stage := by
  classical
  by_cases he : i = j
  · subst j
    exact AlgHom.id R (a i).stage.carrier
  · exact recordMap (a i) (a j) (key i) (hs i j (lt_of_le_of_ne h he))

/-- Diagonal transition maps are identities. -/
private theorem familyMap_self {R : Type u} [CommRing R] {K : Type v} [CommRing K]
    {I L : Type w} [LinearOrder I] (key : I → L)
    (a : I → TowerRecord.{u, v, w} R K L)
    (hs : ∀ i j, i < j → (a j).source (key i) = (a i).stage) (i : I) :
    familyMap key a hs i i le_rfl = AlgHom.id R (a i).stage.carrier := by
  simp [familyMap]

/-- A strict transition is the tagged incoming map of the later stage. -/
private theorem familyMap_strict {R : Type u} [CommRing R] {K : Type v} [CommRing K]
    {I L : Type w} [LinearOrder I] (key : I → L)
    (a : I → TowerRecord.{u, v, w} R K L)
    (hs : ∀ i j, i < j → (a j).source (key i) = (a i).stage)
    (i j : I) (h : i < j) :
    familyMap key a hs i j h.le = recordMap (a i) (a j) (key i) (hs i j h) := by
  simp [familyMap, ne_of_lt h]

/-- Strict composition together with diagonal identities gives a directed system. -/
private theorem familyMap_system {R : Type u} [CommRing R] {K : Type v} [CommRing K]
    {I L : Type w} [LinearOrder I] (key : I → L)
    (a : I → TowerRecord.{u, v, w} R K L)
    (hs : ∀ i j, i < j → (a j).source (key i) = (a i).stage)
    (hc : ∀ i j k (hij : i < j) (hjk : j < k),
      (recordMap (a j) (a k) (key j) (hs j k hjk)).comp
        (recordMap (a i) (a j) (key i) (hs i j hij)) =
      recordMap (a i) (a k) (key i) (hs i k (lt_trans hij hjk))) :
    DirectedSystem (fun i ↦ (a i).stage.carrier) (fun i j h ↦ familyMap key a hs i j h) := by
  constructor
  · intro i x
    rw [familyMap_self]
    rfl
  · intro k j i hij hjk x
    by_cases he : i = j
    · subst j
      rw [familyMap_self]
      rfl
    by_cases he' : j = k
    · subst k
      rw [familyMap_self]
      rfl
    have h₁ := lt_of_le_of_ne hij he
    have h₂ := lt_of_le_of_ne hjk he'
    rw [familyMap_strict key a hs i j h₁, familyMap_strict key a hs j k h₂,
      familyMap_strict key a hs i k (lt_trans h₁ h₂)]
    exact DFunLike.congr_fun (hc i j k h₁ h₂) x

/-- Store a cocone over the predecessors; fill other source tags and maps with identities. -/
private noncomputable def extendRecord {R : Type u} [CommRing R]
    {K : Type v} [CommRing K] {I : Type w} [Preorder I] (i : I)
    (p : ∀ j, j < i → TowerRecord.{u, v, w} R K I)
    (B : TowerStage.{u, v, w} R K) (g : ∀ j (h : j < i), TowerHom (p j h).stage B) :
    TowerRecord.{u, v, w} R K I := by
  classical
  let src : I → TowerStage.{u, v, w} R K := fun j ↦
    if h : j < i then (p j h).stage else B
  refine ⟨B, src, ?_⟩
  intro j
  by_cases h : j < i
  · exact castTowerHom (by simp [src, h]) (g j h)
  · exact castTowerHom (by simp [src, h]) (AlgHom.id R B.carrier)

/-- The extended record stores the exact preceding stage as its source tag. -/
private theorem extendRecord_source {R : Type u} [CommRing R]
    {K : Type v} [CommRing K] {I : Type w} [Preorder I] (i : I)
    (p : ∀ j, j < i → TowerRecord.{u, v, w} R K I)
    (B : TowerStage.{u, v, w} R K) (g : ∀ j (h : j < i), TowerHom (p j h).stage B)
    (j : I) (h : j < i) : (extendRecord i p B g).source j = (p j h).stage := by
  simp [extendRecord, h]

/-- Reading back an incoming map of the extended record recovers the supplied cocone map. -/
private theorem extendRecord_map {R : Type u} [CommRing R]
    {K : Type v} [CommRing K] {I : Type w} [Preorder I] (i : I)
    (p : ∀ j, j < i → TowerRecord.{u, v, w} R K I)
    (B : TowerStage.{u, v, w} R K) (g : ∀ j (h : j < i), TowerHom (p j h).stage B)
    (j : I) (h : j < i) :
    recordMap (p j h) (extendRecord i p B g) j (extendRecord_source i p B g j h) =
      g j h := by
  simp only [recordMap, extendRecord, dite_eq_left h]
  exact castTowerHom_cancel _ _

/-- Source: Stacks Project, Algebra, Lemma 10.159.1 (Tag 03C3), fourth proof paragraph.
(blueprint: new-compatible-ring-tower-recursion)

Proof: Choose a well-order on I and a base stage from hbase. Use ordinary well-founded
recursion on a fixed type of records. A record stores its stage carrier, ring and
R-algebra structures, its map to K, and, for every index of I, an incoming algebra map
with its domain carrier and structures. At index i, test whether the earlier records
form a coherent diagram: their incoming-map domains must agree with the stored earlier
stages, their maps must satisfy the identity and composition laws, and their maps to K
must commute. If they do, and there are predecessors, apply hstep to that diagram on
the strict initial segment and x = q i. Store the resulting stage and cocone maps. If
there are no predecessors, apply hstep to the singleton base diagram and x = q i.
Fill unused incoming-map entries with the identity of the new stage. If the earlier
records are incoherent, use the base record as a default. Fix these choices before
recursing. All records form a type in universe w+1 (or larger to hold the parameters),
so well-founded recursion applies without increasing any carrier's universe.
By well-founded induction the default branch is never used. The cocone equations give
composition with all preceding transitions and compatibility with K; identities give
the diagonal maps. The domains stored in the new record are exactly the previously
chosen carriers. Thus the recursively chosen records give one coherent diagram.
The new stage satisfies P and contains q i by hstep. This also covers finite orders,
orders with limit stages, and the empty order (where the final diagram is empty).
Choices are made inside this existence proof, not used to define any ring. -/
theorem exists_compatible_ring_tower
    (R : Type u) [CommRing R] (K : Type v) [CommRing K]
    (I : Type w) (q : I → K)
    (P : ∀ (A : Type w) [CommRing A] [Algebra R A], (A →+* K) → Prop)
    (hbase : ∃ (A : Type w) (_ : CommRing A) (_ : Algebra R A)
      (ψ : A →+* K), P A ψ)
    (hstep : ∀ (J : Type w) [LinearOrder J] [Nonempty J]
      (A : J → Type w) [∀ j, CommRing (A j)] [∀ j, Algebra R (A j)]
      (f : ∀ i j, i ≤ j → A i →ₐ[R] A j)
      [DirectedSystem A (fun i j h ↦ f i j h)]
      (ψ : ∀ j, A j →+* K),
      (∀ i j h a, ψ j (f i j h a) = ψ i a) →
      (∀ j, P (A j) (ψ j)) → ∀ x : K,
      ∃ (B : Type w) (_ : CommRing B) (_ : Algebra R B) (φ : B →+* K)
        (g : ∀ j, A j →ₐ[R] B),
        (∀ i j h a, g j (f i j h a) = g i a) ∧
        (∀ j a, φ (g j a) = ψ j a) ∧ P B φ ∧ ∃ b, φ b = x) :
    ∃ (_ : LinearOrder I) (A : I → Type w)
      (_ : ∀ i, CommRing (A i)) (_ : ∀ i, Algebra R (A i))
      (f : ∀ i j, i ≤ j → A i →ₐ[R] A j),
      DirectedSystem A (fun i j h ↦ f i j h) ∧
      ∃ (ψ : ∀ i, A i →+* K),
        (∀ i j h a, ψ j (f i j h a) = ψ i a) ∧
        (∀ i, P (A i) (ψ i)) ∧ (∀ i, ∃ a, ψ i a = q i) := by
  classical
  obtain ⟨ord, wf⟩ := exists_wellFoundedLT I
  obtain ⟨A₀, ring₀, alg₀, ψ₀, hP₀⟩ := hbase
  let S₀ : TowerStage.{u, v, w} R K := ⟨A₀, ring₀, alg₀, ψ₀⟩
  let r₀ : TowerRecord.{u, v, w} R K I :=
    ⟨S₀, fun _ ↦ S₀, fun _ ↦ AlgHom.id R A₀⟩
  have hC : ∀ i p, (∀ j (hj : j < i),
      RecordGood q P j (fun k hk ↦ p k (lt_trans hk hj)) (p j hj)) →
      ∃ t, RecordGood q P i p t := by
    intro i p hp
    by_cases hn : Nonempty {j : I // j < i}
    · let J := {j : I // j < i}
      have : Nonempty J := hn
      let a : J → TowerRecord.{u, v, w} R K I := fun j ↦ p j.val j.property
      let hs : ∀ j k : J, j < k → (a k).source j.val = (a j).stage :=
        fun j k hjk ↦ (hp k.val k.property).2.2.choose j.val hjk
      have hc : ∀ j k l (hjk : j < k) (hkl : k < l),
          (recordMap (a k) (a l) k.val (hs k l hkl)).comp
            (recordMap (a j) (a k) j.val (hs j k hjk)) =
          recordMap (a j) (a l) j.val (hs j l (lt_trans hjk hkl)) := by
        intro j k l hjk hkl
        exact (hp l.val l.property).2.2.choose_spec.2 j.val k.val hjk hkl _
      let f : ∀ j k : J, j ≤ k → (a j).stage.carrier →ₐ[R] (a k).stage.carrier :=
        familyMap Subtype.val a hs
      have : DirectedSystem (fun j ↦ (a j).stage.carrier) (fun j k h ↦ f j k h) :=
        familyMap_system Subtype.val a hs hc
      have hψ : ∀ j k h x, (a k).stage.ψ (f j k h x) = (a j).stage.ψ x := by
        intro j k h x
        dsimp only [f]
        by_cases he : j = k
        · subst k
          rw [familyMap_self]
          rfl
        · have hjk := lt_of_le_of_ne h he
          rw [familyMap_strict Subtype.val a hs j k hjk]
          exact (hp k.val k.property).2.2.choose_spec.1 j.val hjk x
      obtain ⟨B, ringB, algB, φ, g, hg, hφ, hPB, hqB⟩ :=
        hstep J (fun j ↦ (a j).stage.carrier) f (fun j ↦ (a j).stage.ψ)
          hψ (fun j ↦ (hp j.val j.property).1) (q i)
      let S : TowerStage.{u, v, w} R K := ⟨B, ringB, algB, φ⟩
      let gg : ∀ j (h : j < i), TowerHom (p j h).stage S := fun j h ↦ g ⟨j, h⟩
      refine ⟨extendRecord i p S gg, hPB, hqB,
        extendRecord_source i p S gg, ?_, ?_⟩
      · intro j hj x
        rw [extendRecord_map]
        exact hφ ⟨j, hj⟩ x
      · intro j k hjk hk he
        rw [extendRecord_map, extendRecord_map]
        ext x
        have h := hg (⟨j, lt_trans hjk hk⟩ : J) ⟨k, hk⟩ hjk.le x
        dsimp only [f] at h
        rw [familyMap_strict Subtype.val a hs _ _ hjk] at h
        exact h
    · let J := ULift.{w} Unit
      let f : ∀ j k : J, j ≤ k → A₀ →ₐ[R] A₀ := fun _ _ _ ↦ AlgHom.id R A₀
      have : DirectedSystem (fun _ : J ↦ A₀) (fun j k h ↦ f j k h) :=
        ⟨fun {_} _ ↦ rfl, fun {_ _ _} _ _ _ ↦ rfl⟩
      obtain ⟨B, ringB, algB, φ, g, hg, hφ, hPB, hqB⟩ :=
        hstep J (fun _ ↦ A₀) f (fun _ ↦ ψ₀) (fun _ _ _ _ ↦ rfl)
          (fun _ ↦ hP₀) (q i)
      let S : TowerStage.{u, v, w} R K := ⟨B, ringB, algB, φ⟩
      have hempty : ∀ j, ¬j < i := fun j hj ↦ hn ⟨⟨j, hj⟩⟩
      let gg : ∀ j (h : j < i), TowerHom (p j h).stage S :=
        fun j h ↦ (hempty j h).elim
      refine ⟨extendRecord i p S gg, hPB, hqB,
        extendRecord_source i p S gg, ?_, ?_⟩
      · intro j hj
        exact (hempty j hj).elim
      · intro j k hjk hk
        exact (hempty k hk).elim
  obtain ⟨a, ha⟩ := coherentChoice r₀ (RecordGood q P) hC
  let hs : ∀ i j, i < j → (a j).source i = (a i).stage :=
    fun i j hij ↦ (ha j).2.2.choose i hij
  have hc : ∀ i j k (hij : i < j) (hjk : j < k),
      (recordMap (a j) (a k) j (hs j k hjk)).comp
        (recordMap (a i) (a j) i (hs i j hij)) =
      recordMap (a i) (a k) i (hs i k (lt_trans hij hjk)) := by
    intro i j k hij hjk
    exact (ha k).2.2.choose_spec.2 i j hij hjk _
  let f : ∀ i j, i ≤ j → (a i).stage.carrier →ₐ[R] (a j).stage.carrier :=
    familyMap id a hs
  refine ⟨ord, fun i ↦ (a i).stage.carrier, fun i ↦ (a i).stage.ring,
    fun i ↦ (a i).stage.alg, f, familyMap_system id a hs hc,
    fun i ↦ (a i).stage.ψ, ?_, fun i ↦ (ha i).1, fun i ↦ (ha i).2.1⟩
  intro i j h x
  dsimp only [f]
  by_cases he : i = j
  · subst j
    rw [familyMap_self]
    rfl
  · have hij := lt_of_le_of_ne h he
    rw [familyMap_strict id a hs i j hij]
    exact (ha j).2.2.choose_spec.1 i hij x

end IsLocalRing
