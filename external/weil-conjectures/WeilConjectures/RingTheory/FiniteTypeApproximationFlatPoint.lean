/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology

import WeilConjectures.RingTheory.LocalizedApproximationColimits
import WeilConjectures.RingTheory.LocalizedApproximationBaseChange
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.RingTheory.ColimitEventuallyFlat
import WeilConjectures.RingTheory.FlatModuleAtPrime

/-! # A flat point in a supplied finite-type approximation

Source: Stacks Project, Tag 02JO (1), proof first paragraph and start of second paragraph.
(blueprint: lem-pc-finite-type-approximation-flat-point)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

set_option autoImplicit false

namespace Algebra

set_option backward.isDefEq.respectTransparency false in
/-- At every prime of the limit, a contracted stage module is flat over its base.

Source: Stacks Project, Algebra, Tag 02JO (1), first paragraph, and Tag 00R6.
(blueprint: lem-pc-finite-type-approximation-flat-point)

Proof:
1. Construct the contracted ring diagrams and the localized module diagram using
   the explicit fraction maps in LocalizedApproximationColimits. Their functor laws
   and semilinearity are proved there; the localized stage squares commute.
2. Finite type over the integers makes A_i Noetherian, and finite type over A_i
   makes B_i Noetherian. Localization preserves Noetherianness and finite modules.
   All localized ring maps are local homomorphisms by localRingHom.
3. localized_approximation_colimits identifies the canonical localized colimits
   and their scalar actions, including flatness over the localized limit base.
   localizedModule_atPrime_of_flat supplies this flatness from the given R-flatness.
4. localized_approximation_baseChange supplies the localized ring localization
   and module tensor equivalence hypotheses. Apply RingTheory.exists_flat_stage
   with these data to obtain flatness over a contracted localized stage base.
5. The fraction formula for localRingHom proves that restriction along A_i to
   its localization agrees with the specified A_i to B_i action on the localized
   stage module. Module.flat_iff_of_isLocalization returns flatness over A_i.
   The two tensor hypotheses for base change to the limit are not needed.
-/
theorem exists_flat_finiteType_approximation_point
    (R S : Type u) (M : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M]
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (A B : Λ ⥤ CommRingCat.{u}) (η : A ⟶ B)
      (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R))
      (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
      (D : Λ ⥤ AddCommGrpCat.{v})
      (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
    [∀ i : Λ, Module (B.obj i) (D.obj i)]
    (hmodel :
      -- (1) the three colimits, compatible with `R → S` and the module actions
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)) ∧
      (∀ i, η.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom (algebraMap R S)) ∧
      (∀ (i j : Λ) (h : i ≤ j) (y : B.obj i) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ i (y : B.obj i) (x : D.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) ∧
      -- (2) finiteness of the stages
      (∀ i, Algebra.FiniteType ℤ (A.obj i)) ∧
      (∀ i, letI := (η.app i).hom.toAlgebra; Algebra.FiniteType (A.obj i) (B.obj i)) ∧
      (∀ i, Module.Finite (B.obj i) (D.obj i)) ∧
      -- (3) transition base changes
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (η.app i).hom.toAlgebra
        letI := (A.map (homOfLE h)).hom.toAlgebra
        ∃ e : B.obj i ⊗[A.obj i] A.obj j ≃+* B.obj j,
          ∀ (x : B.obj i) (y : A.obj j),
            e (x ⊗ₜ[A.obj i] y) = (B.map (homOfLE h)).hom x * (η.app j).hom y) ∧
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (B.map (homOfLE h)).hom.toAlgebra
        ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
          ∀ (y : B.obj j) (x : D.obj i),
            e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x) ∧
      -- (4) base changes to the limit
      (∀ i,
        letI := (η.app i).hom.toAlgebra
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)).toAlgebra
        ∃ e : B.obj i ⊗[A.obj i] R ≃+* S,
          ∀ (x : B.obj i) (y : R),
            e (x ⊗ₜ[A.obj i] y) =
              (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) x * algebraMap R S y) ∧
      (∀ i,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)).toAlgebra
        ∃ e : S ⊗[B.obj i] D.obj i ≃ₗ[S] M,
          ∀ (y : S) (x : D.obj i),
            e (y ⊗ₜ[B.obj i] x) = y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x))
    (hflat : letI : Module R M := Module.compHom M (algebraMap R S)
      Module.Flat R M) :
    ∀ q : PrimeSpectrum S, ∃ i,
      letI : Module (A.obj i)
          (LocalizedModule (PrimeSpectrum.comap (κ.app i).hom q).asIdeal.primeCompl
            (D.obj i)) := Module.compHom _ (η.app i).hom
      Module.Flat (A.obj i)
        (LocalizedModule (PrimeSpectrum.comap (κ.app i).hom q).asIdeal.primeCompl
          (D.obj i)) := by
  classical
  rcases hmodel with
    ⟨hcA, hcB, hcD, hη, hs₀, hν, hfinA, hfinB, hfinD, hr₀, hm₀, _, _⟩
  intro q
  let hs : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : D.obj i),
      (D.map f).hom (b • x) = (B.map f).hom b • (D.map f).hom x :=
    fun i j f b x => hs₀ i j (leOfHom f) b x
  let Aq := primeRingDiagram A (η ≫ κ) q
  let Bq := primeRingDiagram B κ q
  let Nq := primeModuleDiagram B κ q D hs
  let φ := primeDiagramHom A B η κ q
  have hnoethA (i : Λ) : IsNoetherianRing (A.obj i) := by
    have := hfinA i
    exact Algebra.FiniteType.isNoetherianRing ℤ (A.obj i)
  have hnoethB (i : Λ) : IsNoetherianRing (B.obj i) := by
    let := (η.app i).hom.toAlgebra
    have := hnoethA i
    have := hfinB i
    exact Algebra.FiniteType.isNoetherianRing (A.obj i) (B.obj i)
  have : ∀ i, IsLocalRing (Aq.obj i) := fun i => by
    dsimp [Aq, primeRingDiagram]
    infer_instance
  have : ∀ i, IsLocalRing (Bq.obj i) := fun i => by
    dsimp [Bq, primeRingDiagram]
    infer_instance
  have : ∀ i, IsNoetherianRing (Aq.obj i) := fun i => by
    dsimp [Aq, primeRingDiagram]
    have := hnoethA i
    infer_instance
  have : ∀ i, IsNoetherianRing (Bq.obj i) := fun i => by
    dsimp [Bq, primeRingDiagram]
    have := hnoethB i
    infer_instance
  have : ∀ i, Module.Finite (Bq.obj i) (Nq.obj i) := fun i => by
    dsimp [Bq, Nq, primeRingDiagram, primeModuleDiagram]
    have := hfinD i
    exact Module.Finite.of_isLocalizedModule
      (q.asIdeal.comap (κ.app i).hom).primeCompl
      (LocalizedModule.mkLinearMap _ (D.obj i))
  have hφ : ∀ i, IsLocalHom (φ i) := fun i => by
    dsimp [φ, primeDiagramHom]
    exact Localization.isLocalHom_localRingHom _ _ _ _
  have hA : ∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (Aq.map f).hom := by
    intro i j f
    dsimp [Aq, primeRingDiagram]
    exact Localization.isLocalHom_localRingHom _ _ _ _
  have hB : ∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (Bq.map f).hom := by
    intro i j f
    dsimp [Bq, primeRingDiagram]
    exact Localization.isLocalHom_localRingHom _ _ _ _
  have hcomm : ∀ (i j : Λ) (f : i ⟶ j),
      (Bq.map f).hom.comp (φ i) = (φ j).comp (Aq.map f).hom :=
    primeDiagramHom_naturality A B η κ q
  have hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : Bq.obj i) (x : Nq.obj i),
      (Nq.map f).hom (b • x) = (Bq.map f).hom b • (Nq.map f).hom x := by
    intro i j f b x
    exact primeModuleMap_smul _ _ _ (contractedPrime_map B κ q i j f)
      _ (hs i j f) b x
  obtain ⟨ψ, act, hdata⟩ :=
    localized_approximation_colimits R S M A B η π κ D ν hcA hcB hcD hη hs hν q
  let := act
  rcases hdata with ⟨hψ, hlimitScalar, hflatIff⟩
  obtain ⟨hloc, hbase⟩ := localized_approximation_baseChange A B η κ D hs
    (fun i j f => hr₀ i j (leOfHom f)) (fun i j f => hm₀ i j (leOfHom f)) q
  have hflatLocal := Module.Flat.localizedModule_atPrime_of_flat q.asIdeal hflat
  obtain ⟨i, hi⟩ := RingTheory.exists_flat_stage Aq Bq Nq φ hφ hA hB hcomm hscalar
    ψ hψ hlimitScalar hloc hbase (hflatIff.mpr hflatLocal)
  refine ⟨i, ?_⟩
  let p := q.asIdeal.comap ((κ.app i).hom.comp (η.app i).hom)
  let L := LocalizedModule (q.asIdeal.comap (κ.app i).hom).primeCompl (D.obj i)
  let : Module (A.obj i) L := Module.compHom L (η.app i).hom
  let : Module (Localization.AtPrime p) L := Module.compHom L (φ i)
  have : IsScalarTower (A.obj i) (Localization.AtPrime p) L := by
    constructor
    intro r s x
    change φ i (r • s) • x = (η.app i).hom r • (φ i s • x)
    rw [Algebra.smul_def, map_mul]
    dsimp [φ, primeDiagramHom]
    rw [Localization.localRingHom_to_map, mul_smul]
    rw [IsScalarTower.algebraMap_smul (R := B.obj i)
      (A := Localization.AtPrime (q.asIdeal.comap (κ.app i).hom))]
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl L).mp hi

end Algebra
