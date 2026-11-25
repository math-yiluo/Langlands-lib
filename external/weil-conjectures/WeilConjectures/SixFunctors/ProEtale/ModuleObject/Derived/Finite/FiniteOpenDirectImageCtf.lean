/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.FiniteCtfInternalEtaleRealization
import WeilConjectures.AlgebraicGeometry.Finite.Etale.FiniteEtaleOpenUniformTorImage

/-!
# Finite-coefficient open direct image with a uniform Tor interval

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-ctf-stability,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), finite-coefficient open case
(blueprint: lem-sfb-finite-open-direct-image-ctf).

The coefficients are the continuous-map condensed ring of a finite discrete ring, pulled
back from the point. Both categories are the ordinary unbounded derived categories of
internal modules; the direct image is the total right derived module direct image.
-/

@[expose] public section

set_option autoImplicit false

universe u

attribute [instance] Profinite.continuousMapRingObjOfUniverseMonObj
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A quasi-compact open immersion over an arbitrary field of positive characteristic
prime to `ℓ` preserves constant-model bounded constructibility for finite `ℓ`-primary
coefficients and enlarges every Tor interval `[a,b]` to `[a,b+d]` for one fixed `d ≥ 0`.
Tor amplitude tests all degree-zero internal module objects. Zero coefficients and the
zero complex are allowed, and the field need not be separably closed.

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md,
paragraph (3), finite-coefficient open case
(blueprint: lem-sfb-finite-open-direct-image-ctf).

Proof:
Choose the normalized finite-discrete encoding and use the internal-etale realization
for each ordered Tor interval. The etale open-image theorem gives a natural-number
bound d before the input complex and its interval are chosen, including zero rings.
Lift the internal input through the realization equivalence on U. Its etale antecedent
is bounded constructible, hence bounded below. The etale theorem gives a bounded
constructible direct image of amplitude [a,b+d]. Realize this object on X and use the
bounded-below direct-image comparison and the input isomorphism to identify it with
the specified internal direct image. Transport constructibility and Tor amplitude
along this isomorphism. These comparisons also apply to the zero complex and empty
schemes, without a separable-closedness hypothesis on k.
-/
theorem finiteOpenDirectImage_constantModel_torAmplitude
    (ℓ p : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [CharP k p] (_hp : 0 < p) (_hne : p ≠ ℓ)
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (_hA : ∃ n : ℕ, 1 ≤ n ∧ (ℓ : A) ^ n = 0)
    {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [QuasiCompact (U ↘ Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j] :
    ∃ d : ℤ, 0 ≤ d ∧ ∀ (a b : ℤ), a ≤ b →
      ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A) U)),
      constantModelBoundedConstructible
        (Profinite.continuousMapRingObjOfUniverse.{u, u} A) U K →
      DerivedCategory.torAmplitudeIn _ a b K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObjOfUniverse.{u, u} A) X
        ((moduleObjectDerivedPushforward
          (Profinite.continuousMapRingObjOfUniverse.{u, u} A) j).obj K) ∧
      DerivedCategory.torAmplitudeIn _ a (b + d)
        ((moduleObjectDerivedPushforward
          (Profinite.continuousMapRingObjOfUniverse.{u, u} A) j).obj K) := by
  classical
  let E (T : Scheme.{u}) := (FiniteDiscreteOrdinary.encoding_exists A T).some
  obtain ⟨hreal, hpush⟩ := FiniteDiscreteOrdinary.finiteCtfInternalEtaleRealization
    ℓ p k _hp _hne A E
  have hA : ∃ n : ℕ, 1 ≤ n ∧ (ℓ : ULift.{u + 1} A) ^ n = 0 := by
    obtain ⟨n, hn, hnil⟩ := _hA
    refine ⟨n, hn, ?_⟩
    apply ULift.ext
    exact hnil
  obtain ⟨d, _, _, hd⟩ := Etale.finiteEtaleOpen_uniformTorImage
    ℓ p k _hp (Ne.symm _hne) (ULift.{u + 1} A) hA j
  refine ⟨(d : ℤ), Int.natCast_nonneg d, ?_⟩
  intro a b hab K hK htK
  let V : Over (Spec (.of k)) := Over.mk (U ↘ Spec (.of k))
  let T : Over (Spec (.of k)) := Over.mk (X ↘ Spec (.of k))
  have : LocallyOfFiniteType V.hom :=
    inferInstanceAs (LocallyOfFiniteType (U ↘ Spec (.of k)))
  have : QuasiCompact V.hom := inferInstanceAs (QuasiCompact (U ↘ Spec (.of k)))
  have : IsSeparated V.hom := inferInstanceAs (IsSeparated (U ↘ Spec (.of k)))
  have : LocallyOfFiniteType T.hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
  have : QuasiCompact T.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  have : IsSeparated T.hom := inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  let f : V ⟶ T := j.asOver (Spec (.of k))
  obtain ⟨eU, ⟨heU⟩⟩ := hreal V a b hab
  let L := eU.inverse.obj ⟨K, hK, htK⟩
  let eL : (FiniteDiscreteOrdinary.internalEtaleRealization A U (E U)).obj L.obj ≅ K :=
    (heU.app L).symm ≪≫ (ObjectProperty.ι _).mapIso
      (eU.counitIso.app ⟨K, hK, htK⟩)
  obtain ⟨_, hQ, htQ⟩ := hd a b hab L.obj L.property.1 L.property.2
  have habd : a ≤ b + (d : ℤ) := le_trans hab (le_add_of_nonneg_right (by omega))
  obtain ⟨eX, ⟨heX⟩⟩ := hreal T a (b + (d : ℤ)) habd
  let Q := eX.functor.obj ⟨_, hQ, htQ⟩
  have hplus : ∃ n : ℤ, L.obj.IsGE n := by
    obtain ⟨c, e, hce⟩ := L.property.1.2
    exact ⟨c, (DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hce.2 i (Or.inl hi)⟩
  have : QuasiCompact f.left := inferInstanceAs (QuasiCompact j)
  have : QuasiSeparated f.left := inferInstanceAs (QuasiSeparated j)
  obtain ⟨epush⟩ := hpush V T f
  let eQ := (heX.app ⟨_, hQ, htQ⟩) ≪≫ epush.app ⟨L.obj, hplus⟩ ≪≫
    (moduleObjectDerivedPushforward (FiniteDiscreteOrdinary.coefficient A) j).mapIso eL
  have : (constantModelBoundedConstructible
      (FiniteDiscreteOrdinary.coefficient A) X).IsClosedUnderIsomorphisms :=
    (constantModelConstructibleFiniteTor_wellDefined
      (FiniteDiscreteOrdinary.coefficient A) X).2.1
  exact ⟨(constantModelBoundedConstructible
      (FiniteDiscreteOrdinary.coefficient A) X).prop_of_iso eQ Q.property.1,
    (DerivedCategory.torAmplitudeIn (FiniteDiscreteOrdinary.Internal A X)
      a (b + (d : ℤ))).prop_of_iso eQ Q.property.2⟩

end AlgebraicGeometry.ProEtale.CondensedRing
