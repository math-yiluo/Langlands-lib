/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartTriangulated
import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.Pullback.PullbackConstantModelConstructible
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible

/-!
# Rational closed support preserves finite constant constructibility

Source: blueprint main-20261015, chap-Construction-of-f,
`sk-prop-closed-adjoint-constructible-support.md`, final assertion, interpreted with
`definition-constructible-sheaves` (blueprint: lem-sfb-rational-closed-support-constructible).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem finiteConstantLocalModel_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {M N : FormalSupportModules Λ X} (e : M ≅ N)
    (hM : HasFiniteConstantLocalModel Λ X M) : HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 a
  exact ⟨P, hP, ⟨(upperStar Λ (𝒰.f a)).mapIso e.symm ≪≫ eP⟩⟩

private theorem constantModelConstructible_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    {M N : FormalSupportModules Λ X} (e : M ≅ N)
    (hM : IsConstantModelConstructible Λ X M) : IsConstantModelConstructible Λ X N := by
  unfold IsConstantModelConstructible at *
  split_ifs at * with hX
  · obtain ⟨S, hS⟩ := hM
    exact ⟨S, fun a ↦ finiteConstantLocalModel_of_iso Λ _
      ((upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  · intro U hU
    obtain ⟨S, hS⟩ := hM U hU
    exact ⟨S, fun a ↦ finiteConstantLocalModel_of_iso Λ _
      ((upperStar Λ (S.immersion a)).mapIso ((upperStar Λ U.ι).mapIso e)) (hS a)⟩

private theorem constantModel_formalPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : ConstantModelPullbackStatement Λ)
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (f : Y ⟶ X)
    (K : DerivedCategory (FormalSupportModules Λ X))
    (hK : constantModelBoundedConstructible Λ X K) :
    constantModelBoundedConstructible Λ Y
      ((formalSupportPullback Λ f).mapDerivedCategory.obj K) := by
  refine ⟨(formalSupportPullback Λ f).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  apply constantModelConstructible_of_iso Λ Y
    (((formalSupportPullback Λ f).mapDerivedCategoryHomologyFunctorIso n).app K)
  apply constantModelConstructible_of_iso Λ Y
    ((Functor.isoWhiskerLeft
      ((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))).app
        ((DerivedCategory.homologyFunctor _ n).obj K))
  exact (hΛ f _ (hK.2 n)).1

private theorem constantModel_support_of_localization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : ConstantModelPullbackStatement Λ)
    {X Z U : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    [CompactSpace U] [QuasiSeparatedSpace U]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    [(constantModelBoundedConstructible Λ X).IsClosedUnderIsomorphisms]
    [(constantModelBoundedConstructible Λ X).IsTriangulated]
    [(constantModelBoundedConstructible Λ Z).IsClosedUnderIsomorphisms]
    (hpush : ∀ K, constantModelBoundedConstructible Λ U K →
      constantModelBoundedConstructible Λ X ((lowerStar Λ j).rightDerivedFunctor.obj K))
    (K : DerivedCategory (FormalSupportModules Λ X))
    (hK : constantModelBoundedConstructible Λ X K) :
    constantModelBoundedConstructible Λ Z
      ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K) := by
  have hji : Set.range j = (Set.range i)ᶜ := by
    rw [hij, compl_compl]
  obtain ⟨_, _, a, _, _, _, _, _, hc, b, c, δ, _, _, htri, hfiber⟩ :=
    formal_closed_support_adjunction.{u, u + 1} Λ i j hji
  let F := (lowerStar Λ i).mapDerivedCategory.obj
    ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K)
  have hF : constantModelBoundedConstructible Λ X F :=
    (constantModelBoundedConstructible Λ X).ext_of_isTriangulatedClosed₁
      _ (htri K) hK (hpush _ (constantModel_formalPullback Λ hΛ j K hK))
  obtain ⟨e⟩ := hfiber K F (b.counit.app K) (δ.app K) (htri K)
  exact (constantModelBoundedConstructible Λ Z).prop_of_iso e.symm
    (constantModel_formalPullback Λ hΛ i F hF)

/-- Closed support preserves bounded constructible complexes with finite constant scalar
models, both for finite subextensions E of Qbar and for the condensed algebraic closure.
The auxiliary open immersion j presents the complement of the given closed immersion i;
`formalClosedSupport` is the existing functor i* ker(id -> j*j*).

Source: blueprint main-20261015, chap-Construction-of-f,
`sk-prop-closed-adjoint-constructible-support.md`, final assertion and its proof
(blueprint: lem-sfb-rational-closed-support-constructible).

Proof:
1. The field is Noetherian. Finite type makes X and Z Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. X is quasi-separated by
   lem-weil-pbc-locally-noetherian-quasi-separated; the open complement is Noetherian
   and quasi-compact by lem-weil-pbc-noetherian-open-subscheme-noetherian. Thus j is
   quasi-compact by lem-weil-pbc-qcqs-morphism-permanence.
2. For f = i or j, lemma-inverse-image-coefficient-sheaves identifies coefficients and
   gives exact inverse image. Pull back the finite stratification by
   lemma-constructible-pullback-stratification and its local covers. The finite scalar
   matrices of definition-constructible-sheaves--1 pull back to the same matrices;
   exactness preserves their cokernels. By lem-weil-pbc-site-pullback-abelian-exact
   and sk-def-sfb-derived-categories, cohomology pulls back termwise, retaining the
   original finite cohomological interval. Hence i* and j* preserve this Dbc.
3. Clause (4) of lemma-sections-support-closed-subscheme gives the ambient distinguished
   triangle i_* RΓ_Z K -> K -> Rj_* j* K -> (i_* RΓ_Z K)[1], with the canonical unit.
   Its first term F is the fiber of this unit, without a constructibility premise.
4. Step 2 gives j* K in Dbc. Apply lem-sfb-rational-open-direct-image-constructible
   to the quasi-compact j: Rj_* j* K belongs to the same finite-model Dbc.
5. Apply the two-out-of-three and isomorphism closure of
   corollary-coefficient-heart-b--1 to obtain F in Dbc(X).
6. The fiber formula of lemma-sections-support-closed-subscheme identifies RΓ_Z K
   with i* F. Step 2 for i and isomorphism closure give membership in Dbc(Z).
   The argument applies to both coefficient choices separately. -/
theorem rationalClosedSupportConstructible
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {X Z U : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (i : Z ⟶ X) [i.IsOver (Spec (.of k))] [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K : DerivedCategory (FormalSupportModules (Profinite.continuousMapRingObj.{u} E) X)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObj.{u} E) Z
        ((formalClosedSupport (Profinite.continuousMapRingObj.{u} E) i j).rightDerivedFunctor.obj
          K)) ∧
    (∀ K : DerivedCategory (FormalSupportModules (Profinite.padicAlgClRingObj.{u} ℓ) X),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X K →
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Z
        ((formalClosedSupport (Profinite.padicAlgClRingObj.{u} ℓ) i j).rightDerivedFunctor.obj
          K)) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of k))
  have : IsLocallyNoetherian U :=
    isLocallyNoetherian_of_isOpenImmersion j
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Z :=
    QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  have : QuasiCompact j := by infer_instance
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  let : U.Over (Spec (.of k)) := ⟨j ≫ X ↘ Spec (.of k)⟩
  have : j.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : LocallyOfFiniteType (U ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ X ↘ Spec (.of k)))
  have : QuasiCompact (U ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (j ≫ X ↘ Spec (.of k)))
  have : IsSeparated (U ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (j ≫ X ↘ Spec (.of k)))
  have : Fact (ringChar k).Prime := ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by rwa [ringChar.eq k p]⟩
  obtain ⟨hXE, hXbar⟩ := constantModelBoundedConstructible_field_triangulated ℓ X
  obtain ⟨hZE, hZbar⟩ := constantModelBoundedConstructible_field_triangulated ℓ Z
  constructor
  · intro E K hK
    obtain ⟨hXi, hXt, _⟩ := hXE E
    obtain ⟨hZi, _, _⟩ := hZE E
    have hcoeff : ConstantModelPullbackStatement (Profinite.continuousMapRingObj.{u} E) := by
      exact constantModelPullback _
    exact constantModel_support_of_localization _ hcoeff i j hij
      (constantModelBoundedConstructible_rational_open_direct_image ℓ k E j).1 K hK
  · intro K hK
    obtain ⟨hXi, hXt, _⟩ := hXbar
    obtain ⟨hZi, _, _⟩ := hZbar
    have hcoeff : ConstantModelPullbackStatement (Profinite.padicAlgClRingObj.{u} ℓ) := by
      exact constantModelPullback _
    let E : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
    exact constantModel_support_of_localization _ hcoeff i j hij
      (constantModelBoundedConstructible_rational_open_direct_image ℓ k E j).2 K hK

end AlgebraicGeometry.ProEtale.CondensedRing
