/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Finiteness.Ideal
import WeilConjectures.RingTheory.FiniteLengthGlobalSubmodule

/-!
# Krull–Akizuki Noetherianity for intermediate rings

Source: Stacks Project, Algebra, Lemma 10.119.12 (Tag 00PG)
(blueprint: lem-sc-krull-akizuki-noetherian).
-/

@[expose] public section

universe uR uD uK uL

/-- An intermediate ring between a one-dimensional Noetherian domain and a finite
field extension is Noetherian.
Source: Stacks Project, Algebra, Lemma 10.119.12 (Tag 00PG).

Proof:
1. Transfer the domain structure from `L` to `D`. Finite dimensionality makes
   `L` algebraic over `K`, hence over its subring `R` after clearing
   denominators. Injectivity of `D → L` makes `D` algebraic over `R` too.
   Mathlib's `Ideal.comap_ne_bot_of_algebraic_mem` then shows that every
   nonzero ideal `I` contains the image of some nonzero `x : R`.
2. A finite `K`-basis of `L` embeds `D` as an `R`-submodule of a finite power
   of `K`. Apply `lem-sc-finite-length-global-submodule` and transport along
   this embedding to see that `D/xD` is Noetherian over `R`, hence also over
   `D/xD`. Put `J = (x)`, which is contained in `I`. The image of `I` in
   `D/J` is finitely generated, while `I ∩ ker(D → D/J) = J` is principal.
   Mathlib's finite-generation lifting lemma therefore gives `I.FG`.
   The zero ideal is finitely generated separately.
(blueprint: lem-sc-krull-akizuki-noetherian). -/
theorem krullAkizukiNoetherian
    {R : Type uR} {D : Type uD} {K : Type uK} {L : Type uL}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing D] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra R D] [Algebra D L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R D L]
    (hRD : Function.Injective (algebraMap R D))
    (hDL : Function.Injective (algebraMap D L))
    (hdim : ringKrullDim R = 1) :
    IsNoetherianRing D := by
  classical
  let : DistribMulAction R (Submodule R D) := Submodule.pointwiseDistribMulAction
  have : Nontrivial D := hRD.nontrivial
  have : IsDomain D := hDL.isDomain (algebraMap D L)
  have : Algebra.IsAlgebraic R L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := K) (C := L)).mpr inferInstance
  have : Algebra.IsAlgebraic R D :=
    Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom R D L) hDL
  let f : D →ₗ[R] (Fin (Module.finrank K L) → K) :=
    ((Module.finBasis K L).equivFun.restrictScalars R).toLinearMap.comp
      (IsScalarTower.toAlgHom R D L).toLinearMap
  have hf : Function.Injective f :=
    ((Module.finBasis K L).equivFun.injective).comp hDL
  let e : D ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hf
  have hquot (x : R) (hx : x ≠ 0) : IsNoetherian R (QuotSMulTop x D) := by
    have hlen := Submodule.length_quotSMulTop_lt_top_of_ringKrullDim_eq_one
      (Module.finrank K L) (LinearMap.range f) hdim x hx
    have hfinite : IsFiniteLength R (QuotSMulTop x (LinearMap.range f)) :=
      Module.length_ne_top_iff.mp (ne_of_lt hlen)
    have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).1
    exact isNoetherian_of_linearEquiv (QuotSMulTop.congr x e).symm
  apply (isNoetherianRing_iff_ideal_fg D).mpr
  intro I
  by_cases hI : I = ⊥
  · subst I
    exact Submodule.fg_bot
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hcomap := I.under_ne_bot_of_algebraic_mem (R := R) ha0 ha
    (Algebra.IsAlgebraic.isAlgebraic (R := R) a)
  obtain ⟨x, hxI, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomap
  let J : Ideal D := Ideal.span {algebraMap R D x}
  have hJI : J ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hxI
  have hJ : (J.restrictScalars R : Submodule R D) = x • (⊤ : Submodule R D) := by
    ext y
    change y ∈ Ideal.span {algebraMap R D x} ↔ y ∈ x • (⊤ : Submodule R D)
    simp only [Ideal.mem_span_singleton', Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_top, true_and, Algebra.smul_def, mul_comm]
  have : IsNoetherian R (D ⧸ J) := by
    have := hquot x hx
    exact isNoetherian_of_linearEquiv
      ((Submodule.quotEquivOfEq _ _ hJ.symm).trans
        (Submodule.Quotient.restrictScalarsEquiv R J))
  have : IsNoetherianRing (D ⧸ J) := isNoetherian_of_tower R inferInstance
  apply Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective
    (f := Ideal.Quotient.mk J) (Ideal.fg_of_isNoetherianRing _) ?_
    Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker, inf_eq_right.mpr hJI]
  exact Submodule.fg_span_singleton _
