/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Order.DirectedInverseSystem

/-!
# Noetherian local model towers

Source: Stacks Project, Algebra, proof of Tag 00R7, first two paragraphs.
(blueprint: def-weil-pbc-noetherian-local-model-tower).
-/

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace Module

/-- The directed Noetherian model system used in the proof of the fibre criterion.
Source: Stacks Project, Algebra, proof of Tag 00R7, first two paragraphs; the transition
localizations are also the hypotheses of Tag 00R6.
(blueprint: def-weil-pbc-noetherian-local-model-tower).

The ring and module limits are specified elementwise: every element comes from a stage,
and two elements at one stage that agree in the limit agree at a later stage. These
conditions, together with the compatibility clauses, are the filtered colimit universal
property. The last two fields express the limit localization comparisons. No flatness is
part of these data. Both the base-to-top and middle-to-top transition localizations are
retained, since they are used for the base and fibre systems respectively. -/
structure NoetherianLocalModelTower
    (R : Type u) (S : Type v) (S' : Type w) (M : Type t)
    [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M] where
  ι : Type (max u v w)
  [preorder : Preorder ι]
  [nonempty : Nonempty ι]
  [directed : IsDirected ι (· ≤ ·)]
  R₀ : ι → Type (max u v w)
  S₀ : ι → Type (max u v w)
  T₀ : ι → Type (max u v w)
  N₀ : ι → Type t
  [commR : ∀ i, CommRing (R₀ i)]
  [commS : ∀ i, CommRing (S₀ i)]
  [commT : ∀ i, CommRing (T₀ i)]
  [localR : ∀ i, IsLocalRing (R₀ i)]
  [localS : ∀ i, IsLocalRing (S₀ i)]
  [localT : ∀ i, IsLocalRing (T₀ i)]
  [noethR : ∀ i, IsNoetherianRing (R₀ i)]
  [noethS : ∀ i, IsNoetherianRing (S₀ i)]
  [noethT : ∀ i, IsNoetherianRing (T₀ i)]
  [algRS : ∀ i, Algebra (R₀ i) (S₀ i)]
  [algST : ∀ i, Algebra (S₀ i) (T₀ i)]
  [algRT : ∀ i, Algebra (R₀ i) (T₀ i)]
  [towerRST : ∀ i, IsScalarTower (R₀ i) (S₀ i) (T₀ i)]
  [localRS : ∀ i, IsLocalHom (algebraMap (R₀ i) (S₀ i))]
  [localST : ∀ i, IsLocalHom (algebraMap (S₀ i) (T₀ i))]
  [addN : ∀ i, AddCommGroup (N₀ i)]
  [moduleT : ∀ i, Module (T₀ i) (N₀ i)]
  [moduleS : ∀ i, Module (S₀ i) (N₀ i)]
  [moduleR : ∀ i, Module (R₀ i) (N₀ i)]
  [towerSTN : ∀ i, IsScalarTower (S₀ i) (T₀ i) (N₀ i)]
  [towerRSN : ∀ i, IsScalarTower (R₀ i) (S₀ i) (N₀ i)]
  [finite : ∀ i, Module.Finite (T₀ i) (N₀ i)]
  rmap : ∀ i j, i ≤ j → R₀ i →+* R₀ j
  smap : ∀ i j, i ≤ j → S₀ i →+* S₀ j
  tmap : ∀ i j, i ≤ j → T₀ i →+* T₀ j
  nmap : ∀ i j, i ≤ j → N₀ i →+ N₀ j
  rSystem : DirectedSystem R₀ (fun i j h ↦ rmap i j h)
  sSystem : DirectedSystem S₀ (fun i j h ↦ smap i j h)
  tSystem : DirectedSystem T₀ (fun i j h ↦ tmap i j h)
  nSystem : DirectedSystem N₀ (fun i j h ↦ nmap i j h)
  rmap_local : ∀ i j h, IsLocalHom (rmap i j h)
  smap_local : ∀ i j h, IsLocalHom (smap i j h)
  tmap_local : ∀ i j h, IsLocalHom (tmap i j h)
  rs_comm : ∀ i j h, (smap i j h).comp (algebraMap (R₀ i) (S₀ i)) =
    (algebraMap (R₀ j) (S₀ j)).comp (rmap i j h)
  st_comm : ∀ i j h, (tmap i j h).comp (algebraMap (S₀ i) (T₀ i)) =
    (algebraMap (S₀ j) (T₀ j)).comp (smap i j h)
  nmap_smul : ∀ i j h (a : T₀ i) (x : N₀ i),
    nmap i j h (a • x) = tmap i j h a • nmap i j h x
  [algRLimit : ∀ i, Algebra (R₀ i) R]
  [algSLimit : ∀ i, Algebra (S₀ i) S]
  [algTLimit : ∀ i, Algebra (T₀ i) S']
  rlimit_local : ∀ i, IsLocalHom (algebraMap (R₀ i) R)
  slimit_local : ∀ i, IsLocalHom (algebraMap (S₀ i) S)
  tlimit_local : ∀ i, IsLocalHom (algebraMap (T₀ i) S')
  rlimit_comm : ∀ i j h,
    (algebraMap (R₀ j) R).comp (rmap i j h) = algebraMap (R₀ i) R
  slimit_comm : ∀ i j h,
    (algebraMap (S₀ j) S).comp (smap i j h) = algebraMap (S₀ i) S
  tlimit_comm : ∀ i j h,
    (algebraMap (T₀ j) S').comp (tmap i j h) = algebraMap (T₀ i) S'
  rs_limit_comm : ∀ i, (algebraMap (S₀ i) S).comp (algebraMap (R₀ i) (S₀ i)) =
    (algebraMap R S).comp (algebraMap (R₀ i) R)
  st_limit_comm : ∀ i, (algebraMap (T₀ i) S').comp (algebraMap (S₀ i) (T₀ i)) =
    (algebraMap S S').comp (algebraMap (S₀ i) S)
  nlimit : ∀ i, N₀ i →+ M
  nlimit_comm : ∀ i j h, (nlimit j).comp (nmap i j h) = nlimit i
  nlimit_smul : ∀ i (a : T₀ i) (x : N₀ i),
    nlimit i (a • x) = algebraMap (T₀ i) S' a • nlimit i x
  rlimit_surj : ∀ r : R, ∃ i, ∃ x : R₀ i, algebraMap (R₀ i) R x = r
  slimit_surj : ∀ s : S, ∃ i, ∃ x : S₀ i, algebraMap (S₀ i) S x = s
  tlimit_surj : ∀ s : S', ∃ i, ∃ x : T₀ i, algebraMap (T₀ i) S' x = s
  nlimit_surj : ∀ m : M, ∃ i, ∃ x : N₀ i, nlimit i x = m
  rlimit_eq : ∀ i (x y : R₀ i), algebraMap (R₀ i) R x = algebraMap (R₀ i) R y →
    ∃ j, ∃ h : i ≤ j, rmap i j h x = rmap i j h y
  slimit_eq : ∀ i (x y : S₀ i), algebraMap (S₀ i) S x = algebraMap (S₀ i) S y →
    ∃ j, ∃ h : i ≤ j, smap i j h x = smap i j h y
  tlimit_eq : ∀ i (x y : T₀ i), algebraMap (T₀ i) S' x = algebraMap (T₀ i) S' y →
    ∃ j, ∃ h : i ≤ j, tmap i j h x = tmap i j h y
  nlimit_eq : ∀ i (x y : N₀ i), nlimit i x = nlimit i y →
    ∃ j, ∃ h : i ≤ j, nmap i j h x = nmap i j h y
  baseTransition : ∀ i j (h : i ≤ j),
    letI := (rmap i j h).toAlgebra
    ∃ (f : T₀ i ⊗[R₀ i] R₀ j →+* T₀ j)
      (U : Submonoid (T₀ i ⊗[R₀ i] R₀ j)),
      (∀ (a : T₀ i) (b : R₀ j), f (a ⊗ₜ[R₀ i] b) = tmap i j h a *
        algebraMap (R₀ j) (T₀ j) b) ∧ (letI := f.toAlgebra; IsLocalization U (T₀ j))
  fibreTransition : ∀ i j (h : i ≤ j),
    letI := (smap i j h).toAlgebra
    ∃ (f : T₀ i ⊗[S₀ i] S₀ j →+* T₀ j)
      (U : Submonoid (T₀ i ⊗[S₀ i] S₀ j)),
      (∀ (a : T₀ i) (b : S₀ j), f (a ⊗ₜ[S₀ i] b) = tmap i j h a *
        algebraMap (S₀ j) (T₀ j) b) ∧ (letI := f.toAlgebra; IsLocalization U (T₀ j))
  moduleTransition : ∀ i j (h : i ≤ j),
    letI := (tmap i j h).toAlgebra
    ∃ e : (T₀ j ⊗[T₀ i] N₀ i) ≃ₗ[T₀ j] N₀ j,
      ∀ (a : T₀ j) (x : N₀ i), e (a ⊗ₜ[T₀ i] x) = a • nmap i j h x
  baseLocalization : ∀ i, ∃ U : Submonoid (R ⊗[R₀ i] S₀ i),
    Nonempty (LocalizedModule U (R ⊗[R₀ i] S₀ i) ≃ₗ[R] S)
  moduleLocalization : ∀ i,
    ∃ (_ : Module (S ⊗[S₀ i] T₀ i) (S ⊗[S₀ i] N₀ i))
      (_ : IsScalarTower S (S ⊗[S₀ i] T₀ i) (S ⊗[S₀ i] N₀ i))
      (U : Submonoid (S ⊗[S₀ i] T₀ i)),
      Nonempty (LocalizedModule U (S ⊗[S₀ i] N₀ i) ≃ₗ[S] M)

end Module
