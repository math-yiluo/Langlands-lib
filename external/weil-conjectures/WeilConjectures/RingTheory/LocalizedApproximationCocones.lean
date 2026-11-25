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
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Localization.Defs

import WeilConjectures.RingTheory.CanonicalLocalizedApproximationLimit
import WeilConjectures.RingTheory.LocalizedApproximationColimits

/-! # Cocones for prime-localized approximation diagrams

Source: Stacks Project, Algebra, Tag 00RC, first reduction, and Tag 037D.
(blueprint: lem-weil-pbc-localized-approximation-cocones)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

private theorem localized_compHom_eq
    {T U N : Type*} [CommRing T] [CommRing U] [Algebra T U]
    [AddCommGroup N] [Module T N] [Module U N] [IsScalarTower T U N] :
    Module.compHom N (algebraMap T U) = (inferInstance : Module T N) :=
  Module.ext' _ _ fun r x ↦ IsScalarTower.algebraMap_smul U r x

private theorem module_identity_equiv
    {T N : Type*} [CommRing T] [AddCommGroup N]
    (P Q : Module T N) (h : P = Q) :
    Nonempty (@LinearEquiv T T _ _ (RingHom.id T)
      (RingHom.id T) _ _ N N _ _ P Q) := by
  subst Q
  let := P
  exact ⟨LinearEquiv.refl T N⟩

private theorem linearMap_heq_of_module_eq
    {T N L : Type*} [CommRing T] [AddCommGroup N] [AddCommGroup L] [Module T N]
    (P Q : Module T L) (h : P = Q)
    (f : letI := P; N →ₗ[T] L) (g : letI := Q; N →ₗ[T] L)
    (hfg : ∀ x, f x = g x) : HEq f g := by
  subst Q
  let := P
  exact heq_of_eq (LinearMap.ext hfg)

private theorem prime_ring_localization_witness
    {T : Type*} [CommRing T] (p : Ideal T) [p.IsPrime] :
    let ρ := algebraMap T (Localization.AtPrime p)
    letI := ρ.toAlgebra
    IsLocalization p.primeCompl (Localization.AtPrime p) := by
  change @IsLocalization T _ p.primeCompl (Localization.AtPrime p) _
    (algebraMap T (Localization.AtPrime p)).toAlgebra
  rw [toAlgebra_algebraMap]
  infer_instance

set_option linter.unusedVariables false in
/-- Construct the localized ring and module cocones, without finiteness or tensor hypotheses.

Source: Stacks Project, Algebra, Tag 00RC, first reduction paragraph; Tag 037D.
(blueprint: lem-weil-pbc-localized-approximation-cocones)

Proof:
1. Contract q along each top-stage cocone map followed by ULift.down and then along
   the base-to-top map. Cocone naturality and the commuting squares identify the
   contractions along transitions. Take Localization.AtPrime of both stage rings
   and LocalizedModule of each stage module. The transition maps send x/s to
   f(x)/f(s). They are well defined because a denominator outside the earlier prime
   maps outside the later prime; semilinearity carries the fraction relation to the
   fraction relation. Uniqueness on numerator-one images proves the functor laws,
   the ring squares, and all displayed naturality identities for the maps ρA, ρB, ζ.
2. Localize the two supplied ring colimit cocones using Tag 037D. Transport their
   colimit comparisons through the canonical ULift ring equivalences. For modules,
   lift a numerator and denominator to a common stage. Equality of fractions has
   a multiplier outside q; lift that multiplier and descend the zero relation to
   a later stage using eventual equality in the supplied group colimit. This gives
   the localized group colimit and its scalar action by multiplication of fractions.
   The cocone maps are semilinear for this action. The commuting ring squares induce ψ.
3. Prime localizations are local. A fraction is a nonunit precisely when its numerator
   belongs to the contracted prime; this criterion proves locality of every induced
   ring map.
4. The base limit is R at q contracted to R. The module limit is M at q. The fraction
   comparisons preserve the restricted R-action, giving the limit linear equivalence.
   At each stage the same calculation gives the A_i-linear module equivalence and
   base localization witness. The numerator-one linear map ℓ is IsLocalizedModule:
   denominator scalars are invertible, every fraction has a numerator and denominator,
   and an equality of numerator-one images is killed by a denominator.
No Noetherianity, finiteness, or transition tensor equivalence is needed here. -/
theorem exists_localized_approximation_cocones
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    let R' := ULift.{max u v w} R
    let S' := ULift.{max u v w} S
    let M' := ULift.{max u v w} M
    letI : Algebra R' S' := ULift.algebra' R S'
    ∀
    {Λ : Type (max u v w)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (A B : Λ ⥤ CommRingCat.{max u v w}) (η : A ⟶ B)
      (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R'))
      (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S'))
      (D : Λ ⥤ AddCommGrpCat.{max u v w})
      (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M'))
    [∀ i : Λ, Module (B.obj i) (D.obj i)]
    (hmodel :
      -- (1) the three colimits, compatible with `R' → S'` and the module actions
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R') π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S') κ)) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M') ν)) ∧
      (∀ i, η.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom (algebraMap R' S')) ∧
      (∀ (i j : Λ) (h : i ≤ j) (y : B.obj i) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ i (y : B.obj i) (x : D.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M') (ν.app i)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ.app i)) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M') (ν.app i)) x))
    (q : PrimeSpectrum S),
    ∃ (Aₗ Bₗ : Λ ⥤ CommRingCat.{max u v w})
      (Dₗ : Λ ⥤ AddCommGrpCat.{max u v w}),
    ∃ hcA : HasColimit Aₗ, letI := hcA
    ∃ hcB : HasColimit Bₗ, letI := hcB
    ∃ hcD : HasColimit Dₗ, letI := hcD
    ∃ hlocalA : ∀ i, IsLocalRing (Aₗ.obj i), letI := hlocalA
    ∃ hlocalB : ∀ i, IsLocalRing (Bₗ.obj i), letI := hlocalB
    ∃ hmodule : ∀ i, Module (Bₗ.obj i) (Dₗ.obj i), letI := hmodule
    ∃ hmoduleLimit : Module (colimit Bₗ : CommRingCat.{max u v w})
        (colimit Dₗ : AddCommGrpCat.{max u v w}), letI := hmoduleLimit
    ∃ (φ : ∀ i, Aₗ.obj i →+* Bₗ.obj i)
      (ψ : (colimit Aₗ : CommRingCat.{max u v w}) →+*
        (colimit Bₗ : CommRingCat.{max u v w})),
      (∀ i, IsLocalHom (φ i)) ∧
      (∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (Aₗ.map f).hom) ∧
      (∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (Bₗ.map f).hom) ∧
      (∀ (i j : Λ) (f : i ⟶ j),
        (Bₗ.map f).hom.comp (φ i) = (φ j).comp (Aₗ.map f).hom) ∧
      (∀ (i j : Λ) (f : i ⟶ j) (b : Bₗ.obj i) (x : Dₗ.obj i),
        (Dₗ.map f).hom (b • x) = (Bₗ.map f).hom b • (Dₗ.map f).hom x) ∧
      (∀ i, ψ.comp (colimit.ι Aₗ i).hom = (colimit.ι Bₗ i).hom.comp (φ i)) ∧
      (∀ (i : Λ) (b : Bₗ.obj i) (x : Dₗ.obj i),
        (colimit.ι Dₗ i).hom (b • x) =
          (colimit.ι Bₗ i).hom b • (colimit.ι Dₗ i).hom x) ∧
      (∃ ρ : R →+* (colimit Aₗ : CommRingCat.{max u v w}),
        letI := ρ.toAlgebra
        letI := Module.compHom (colimit Dₗ : AddCommGrpCat.{max u v w}) ψ
        letI := Module.compHom (colimit Dₗ : AddCommGrpCat.{max u v w}) ρ
        IsLocalization (q.asIdeal.comap (algebraMap R S)).primeCompl
          (colimit Aₗ : CommRingCat.{max u v w}) ∧
        Nonempty (LocalizedModule q.asIdeal.primeCompl M ≃ₗ[R]
          (colimit Dₗ : AddCommGrpCat.{max u v w}))) ∧
      (∀ i, ∃ ρ : A.obj i →+* Aₗ.obj i,
        letI := (φ i).toAlgebra
        letI := Module.compHom (Dₗ.obj i) (φ i)
        letI := ρ.toAlgebra
        letI := Module.compHom (Dₗ.obj i) ρ
        letI : Algebra (A.obj i) (B.obj i) := (η.app i).hom.toAlgebra
        letI : Module (A.obj i) (D.obj i) := Module.compHom (D.obj i) (η.app i).hom
        letI : IsScalarTower (A.obj i) (B.obj i) (D.obj i) :=
          IsScalarTower.of_compHom _ _ _
        IsLocalization
          (q.asIdeal.comap ((ULift.ringEquiv.toRingHom.comp (κ.app i).hom).comp
            (η.app i).hom)).primeCompl (Aₗ.obj i) ∧
        Nonempty (LocalizedModule
          (q.asIdeal.comap (ULift.ringEquiv.toRingHom.comp (κ.app i).hom)).primeCompl
          (D.obj i) ≃ₗ[A.obj i] Dₗ.obj i)) ∧
      (∃ (ρA : ∀ i, A.obj i →+* Aₗ.obj i)
        (ρB : ∀ i, B.obj i →+* Bₗ.obj i)
        (ζ : ∀ i, D.obj i →+ Dₗ.obj i),
        (∀ i, letI := (ρA i).toAlgebra
          IsLocalization
            (q.asIdeal.comap ((ULift.ringEquiv.toRingHom.comp (κ.app i).hom).comp
              (η.app i).hom)).primeCompl (Aₗ.obj i)) ∧
        (∀ i, letI := (ρB i).toAlgebra
          IsLocalization
            (q.asIdeal.comap (ULift.ringEquiv.toRingHom.comp (κ.app i).hom)).primeCompl
            (Bₗ.obj i)) ∧
        (∀ i, (ρB i).comp (η.app i).hom = (φ i).comp (ρA i)) ∧
        (∀ (i j : Λ) (f : i ⟶ j),
          (ρA j).comp (A.map f).hom = (Aₗ.map f).hom.comp (ρA i)) ∧
        (∀ (i j : Λ) (f : i ⟶ j),
          (ρB j).comp (B.map f).hom = (Bₗ.map f).hom.comp (ρB i)) ∧
        (∀ (i j : Λ) (f : i ⟶ j) (x : D.obj i),
          ζ j ((D.map f).hom x) = (Dₗ.map f).hom (ζ i x)) ∧
        (∀ i (b : B.obj i) (x : D.obj i), ζ i (b • x) = ρB i b • ζ i x) ∧
        (∀ i, letI := Module.compHom (Dₗ.obj i) (ρB i)
          ∃ ℓ : D.obj i →ₗ[B.obj i] Dₗ.obj i,
            (∀ x, ℓ x = ζ i x) ∧
            IsLocalizedModule
              (q.asIdeal.comap (ULift.ringEquiv.toRingHom.comp (κ.app i).hom)).primeCompl
              ℓ)) := by
  classical
  dsimp only
  intro Λ _ _ _ A B η π κ D ν _ hmodel q
  let q' : PrimeSpectrum (ULift.{max u v w} S) :=
    ⟨q.asIdeal.comap ULift.ringEquiv.toRingHom, Ideal.IsPrime.comap _⟩
  let hs := fun (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : D.obj i) ↦
    hmodel.2.2.2.2.1 i j (leOfHom f) b x
  let Aₗ := primeRingDiagram A (η ≫ κ) q'
  let Bₗ := primeRingDiagram B κ q'
  let Dₗ := primeModuleDiagram B κ q' D hs
  let φ := primeDiagramHom A B η κ q'
  let : Algebra (ULift.{max u v w} R) (ULift.{max u v w} S) :=
    ULift.algebra' R (ULift.{max u v w} S)
  obtain ⟨ψ, act, hψ, hscalarLimit, _⟩ :=
    localized_approximation_colimits (ULift.{max u v w} R) (ULift.{max u v w} S)
      (ULift.{max u v w} M) A B η π κ D ν hmodel.1 hmodel.2.1 hmodel.2.2.1
      hmodel.2.2.2.1 hs hmodel.2.2.2.2.2 q'
  let := act
  have hlimit := canonical_localized_approximation_limit R S M A B η π κ D ν
    hmodel q ψ act hψ hscalarLimit
  have hQA (i : Λ) :
      q.asIdeal.comap ((ULift.ringEquiv.toRingHom.comp (κ.app i).hom).comp
        (η.app i).hom) = q'.asIdeal.comap ((η ≫ κ).app i).hom := by
    simp only [q', Ideal.comap_comap, RingHom.comp_assoc]
    rfl
  have hQB (i : Λ) :
      q.asIdeal.comap (ULift.ringEquiv.toRingHom.comp (κ.app i).hom) =
        q'.asIdeal.comap (κ.app i).hom := by
    rw [Ideal.comap_comap]
  let localA : ∀ i, IsLocalRing (Aₗ.obj i) := fun i => inferInstance
  let localB : ∀ i, IsLocalRing (Bₗ.obj i) := fun i => inferInstance
  let modules : ∀ i, Module (Bₗ.obj i) (Dₗ.obj i) := fun i => inferInstance
  let := act
  refine ⟨Aₗ, Bₗ, Dₗ, inferInstance, inferInstance, inferInstance,
    localA, localB, modules, act, φ, ψ, ?_, ?_, ?_, ?_, ?_,
    hψ, hscalarLimit, hlimit, ?_, ?_⟩
  · intro i
    exact Localization.isLocalHom_localRingHom _ _ _ rfl
  · intro i j f
    exact Localization.isLocalHom_localRingHom _ _ _
      (contractedPrime_map A (η ≫ κ) q' i j f)
  · intro i j f
    exact Localization.isLocalHom_localRingHom _ _ _
      (contractedPrime_map B κ q' i j f)
  · intro i j f
    exact primeDiagramHom_naturality A B η κ q' i j f
  · intro i j f b x
    exact primeModuleMap_smul _ _ _ (contractedPrime_map B κ q' i j f)
      _ (hs i j f) b x
  · intro i
    simp only [hQA i]
    let : Algebra (A.obj i) (B.obj i) := (η.app i).hom.toAlgebra
    let : Module (A.obj i) (D.obj i) := Module.compHom (D.obj i) (η.app i).hom
    let : IsScalarTower (A.obj i) (B.obj i) (D.obj i) :=
      IsScalarTower.of_compHom _ _ _
    refine ⟨algebraMap (A.obj i) (Aₗ.obj i), ?_, ?_⟩
    · exact prime_ring_localization_witness _
    · let src : Module (A.obj i) (Dₗ.obj i) := inferInstance
      let dst : Module (A.obj i) (Dₗ.obj i) :=
        letI := Module.compHom (Dₗ.obj i) (φ i)
        Module.compHom (Dₗ.obj i) (algebraMap (A.obj i) (Aₗ.obj i))
      have hact : src = dst := by
        apply Module.ext'
        intro a x
        change _ =
          (φ i) (algebraMap (A.obj i) (Aₗ.obj i) a) • x
        exact (IsScalarTower.algebraMap_smul (B.obj i) a x).symm.trans
          ((IsScalarTower.algebraMap_smul (Bₗ.obj i) ((η.app i).hom a) x).symm.trans
            (congrArg (fun b : Bₗ.obj i ↦ b • x)
              (Localization.localRingHom_to_map _ _ (η.app i).hom rfl a).symm))
      exact module_identity_equiv src dst hact
  · let ρA := fun i => algebraMap (A.obj i) (Aₗ.obj i)
    let ρB := fun i => algebraMap (B.obj i) (Bₗ.obj i)
    let ζ := fun i => (LocalizedModule.mkLinearMap
      (q'.asIdeal.comap (κ.app i).hom).primeCompl (D.obj i)).toAddMonoidHom
    refine ⟨ρA, ρB, ζ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simp only [hQA i]
      exact prime_ring_localization_witness _
    · intro i
      simp only [hQB i]
      exact prime_ring_localization_witness _
    · intro i
      ext a
      exact (Localization.localRingHom_to_map _ _ _ rfl a).symm
    · intro i j f
      ext a
      exact (Localization.localRingHom_to_map _ _ _
        (contractedPrime_map A (η ≫ κ) q' i j f) a).symm
    · intro i j f
      ext b
      exact (Localization.localRingHom_to_map _ _ _
        (contractedPrime_map B κ q' i j f) b).symm
    · intro i j f x
      dsimp [ζ, Dₗ, primeModuleDiagram]
      simp only [LocalizedModule.mkLinearMap_apply, primeModuleMap_mk]
      congr 1
      apply Subtype.ext
      exact (map_one (B.map f).hom).symm
    · intro i b x
      dsimp [ζ, ρB]
      rw [IsScalarTower.algebraMap_smul]
      exact (LocalizedModule.mkLinearMap _ (D.obj i)).map_smul b x
    · intro i
      simp only [hQB i]
      have hscalar (b : B.obj i) (x : D.obj i) :
          ζ i (b • x) = ρB i b • ζ i x := by
        dsimp [ζ, ρB]
        rw [IsScalarTower.algebraMap_smul]
        exact (LocalizedModule.mkLinearMap _ (D.obj i)).map_smul b x
      have hmod := localized_compHom_eq
        (T := B.obj i) (U := Bₗ.obj i) (N := Dₗ.obj i)
      have hloc := localizedModuleIsLocalizedModule
        (S := (q'.asIdeal.comap (κ.app i).hom).primeCompl) (M := D.obj i)
      let : Module (B.obj i) (Dₗ.obj i) := Module.compHom (Dₗ.obj i) (ρB i)
      refine ⟨{ toFun := fun x ↦ ζ i x
                map_add' := (ζ i).map_add
                map_smul' := ?_ }, fun x ↦ rfl, ?_⟩
      · exact hscalar
      · convert! hloc using 1
        exact linearMap_heq_of_module_eq _ _ hmod _ _ (fun x ↦ rfl)

end Algebra
