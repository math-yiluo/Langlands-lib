/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalClosedSupportConstructible
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.CategoryTheory.Yoneda

/-!
# Closed exceptional inverse image and sections with support

Source: blueprint main-20261015, chap-Construction-of-f,
sk-prop-closed-adjoint-constructible/sk-prop-closed-adjoint-constructible-yoneda.md
(blueprint: theorem-f-shriek-ell-adic-coefficients).

The comparison lives in the full localizing category, and its counit equation is written
in the ambient derived category using the specified closed-immersion normalization.
The algebraic-closure coefficient is the finite-subextension-valued condensed ring.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Exact coefficient restriction preserves and reflects cohomology and finite constant models.
private theorem bounded_comap_iff
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] [IsIso a] (X : Scheme.{u})
    (K : DerivedCategory (FormalSupportModules Λ' X)) :
    constantModelBoundedConstructible Λ X
        ((Mod.comap (coefficientMap a X)).mapDerivedCategory.obj K) ↔
      constantModelBoundedConstructible Λ' X K := by
  let F : FormalSupportModules Λ' X ⥤ FormalSupportModules Λ X :=
    Mod.comap (coefficientMap a X)
  have hmod (M : FormalSupportModules Λ' X) :
      IsConstantModelConstructible Λ X ((Mod.comap (coefficientMap a X)).obj M) ↔
        IsConstantModelConstructible Λ' X M := by
    constructor
    · intro hM
      have hback := constructible_comap (inv a) X _ hM
      exact constructible_iso
        (((Mod.comapComp (coefficientMap (inv a) X) (coefficientMap a X)).symm ≪≫
          Mod.comapCongr (by rw [← coefficientMap_comp]; simp) ≪≫
            Mod.comapId _).app M) hback
    · exact constructible_comap a X M
  constructor
  · intro h
    refine ⟨F.bounded_of_bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
    apply (hmod _).mp
    exact constructible_iso
      ((F.mapDerivedCategoryHomologyFunctorIso n).app K).symm (h.2 n)
  · intro h
    refine ⟨F.bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
    exact constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
      ((hmod _).mpr (h.2 n))

-- Conjugate closed direct image by coefficient equivalences and use right-adjoint uniqueness.
private theorem support_preserved_of_coefficientIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ')
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (hpres : ∀ K, constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ Z
        ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K)) :
    ∀ K, constantModelBoundedConstructible Λ' X K →
      constantModelBoundedConstructible Λ' Z
        ((formalClosedSupport Λ' i j).rightDerivedFunctor.obj K) := by
  let a := e.hom.hom
  have : IsMonHom a := inferInstanceAs (IsMonHom e.hom.hom)
  have : IsIso a := inferInstanceAs (IsIso e.hom.hom)
  let R (T : Scheme.{u}) : FormalSupportModules Λ' T ⥤ FormalSupportModules Λ T :=
    Mod.comap (coefficientMap a T)
  let E₀ (T : Scheme.{u}) := Mod.comapEquivalenceOfIsIso
    (C := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (coefficientMap a T)
  have (T : Scheme.{u}) : (E₀ T).functor.Additive := inferInstanceAs (R T).Additive
  have (T : Scheme.{u}) : (E₀ T).inverse.Additive :=
    inferInstanceAs (Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (asIso (coefficientMap a T)).inv).Additive
  let E (T : Scheme.{u}) := (E₀ T).mapDerivedCategory
  have hji : Set.range j = (Set.range i)ᶜ := by rw [hij, compl_compl]
  obtain ⟨_, _, b, _⟩ := formal_closed_support_adjunction Λ i j hji
  obtain ⟨_, _, b', _⟩ := formal_closed_support_adjunction Λ' i j hji
  let := b.leftAdjoint_preservesColimits
  let := b'.leftAdjoint_preservesColimits
  let F := (lowerStar Λ i).mapDerivedCategory
  let F' := (lowerStar Λ' i).mapDerivedCategory
  let S := (formalClosedSupport Λ i j).rightDerivedFunctor
  let S' := (formalClosedSupport Λ' i j).rightDerivedFunctor
  let q : F' ⋙ (E X).functor ≅ (E Z).functor ⋙ F :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (comapLowerStarIso a i) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
  let q' : (E Z).inverse ⋙ F' ⋙ (E X).functor ≅ F :=
    Functor.isoWhiskerLeft (E Z).inverse q ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E Z).counitIso F ≪≫ F.leftUnitor
  let bconj := ((E Z).symm.toAdjunction.comp
    b'.mapDerivedCategoryRightDerivedAdjunction).comp (E X).toAdjunction
  let r : S ≅ (E X).inverse ⋙ S' ⋙ (E Z).functor :=
    b.mapDerivedCategoryRightDerivedAdjunction.rightAdjointUniq
      (bconj.ofNatIsoLeft q')
  let t : (E X).functor ⋙ S ≅ S' ⋙ (E Z).functor :=
    Functor.isoWhiskerLeft (E X).functor r ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E X).unitIso.symm (S' ⋙ (E Z).functor) ≪≫
      (S' ⋙ (E Z).functor).leftUnitor
  intro K hK
  apply (bounded_comap_iff a Z _).mp
  have hiso := (constantModelConstructibleFiniteTor_wellDefined Λ Z).2.1
  let := hiso
  exact (constantModelBoundedConstructible Λ Z).prop_of_iso (t.app K)
    (hpres _ ((bounded_comap_iff a X K).mpr hK))

-- The proof compares two Hom equivalences in full derived subcategories.
/-- On bounded constructible inputs the exceptional right adjoint is naturally isomorphic
to derived sections with support, compatibly with their counits. The witnesses `hK` and
`hS` only record membership in the full localizing subcategories: the two lifted functors
have exactly the ambient objects and maps. The isomorphism `closed` is the stipulated
normalization Ri_! = i_*, and `support` specifies the normalized support adjunction.

Source: blueprint main-20261015, sk-prop-closed-adjoint-constructible-yoneda, statement
and proof (blueprint: theorem-f-shriek-ell-adic-coefficients).

Proof:
1. The equality Dctf = Dbc from det-def-localizing-closure-ctf-equals-bc and the intersection
   definition-localizing-subcategory put every input K in C_X. The adjunction of
   theorem-existence-exceptional-inverse-image puts i^!K in C_Z. By
   lem-sfb-rational-closed-support-constructible, RΓ_Z K is Dbc, hence belongs to C_Z.
   Exact coefficient equivalences transport this assertion to the given ring isomorphism.
   Both localizing categories are full in the ambient derived categories.
2. For A in C_Z the two adjunctions identify Hom(A,i^!K) and Hom(A,RΓ_Z K) with
   Hom(i_*A,K), by a mapped arrow followed by the respective counit. These bijections
   are natural in A and K. Compose the first with the inverse of the second.
3. By lem-galois-yoneda-fully-faithful, this natural transformation and its inverse
   come from mutually inverse maps θ_K and ρ_K in C_Z. Evaluation at the identity
   gives i_*(θ_K) followed by the support counit equal to the exceptional counit,
   with the latter transported along `closed`. Injectivity of the support adjunction
   bijection gives uniqueness of the map satisfying this equation.
4. For q : K → K', naturality of the two counits gives the same transpose for
   RΓ_Z(q) θ_K and θ_K' i^!(q). Injectivity gives equality, hence a natural
   isomorphism. Cohomology of this isomorphism also transfers boundedness and
   constructibility from the support value to i^!K.
-/
theorem closedAdjointConstructibleYoneda
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {X Z U : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (c : Compactification.BoundaryCompactification i)
    (h : ∀ K, localizingClosureProEtale Λ Z K → localizingClosureProEtale Λ X
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ Z).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G) :
    letI := closedSupport_lowerStarExact Λ i j hij
    ∀ (closed : localizingLowerShriek Λ c.obj.obj h ⋙ (localizingClosureProEtale Λ X).ι ≅
      (localizingClosureProEtale Λ Z).ι ⋙ (lowerStar Λ i).mapDerivedCategory)
      (support : FormalClosedSupportAssertions Λ i j hij),
    ∃ (hK : ∀ K : ConstantModelBoundedConstructible Λ X,
        localizingClosureProEtale Λ X K.obj)
      (hS : ∀ K : ConstantModelBoundedConstructible Λ X,
        localizingClosureProEtale Λ Z
          ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)),
      ∃ e :
        ((localizingClosureProEtale Λ X).lift
          (constantModelBoundedConstructible Λ X).ι hK) ⋙ G ≅
        (localizingClosureProEtale Λ Z).lift
          ((constantModelBoundedConstructible Λ X).ι ⋙
            (formalClosedSupport Λ i j).rightDerivedFunctor) hS,
        ∀ K : ConstantModelBoundedConstructible Λ X,
          (lowerStar Λ i).mapDerivedCategory.map
              ((localizingClosureProEtale Λ Z).ι.map (e.hom.app K)) ≫
            support.rightAdjoint.counit.app K.obj =
          closed.inv.app (G.obj (((localizingClosureProEtale Λ X).lift
            (constantModelBoundedConstructible Λ X).ι hK).obj K)) ≫
            (localizingClosureProEtale Λ X).ι.map
              (adj.counit.app (((localizingClosureProEtale Λ X).lift
                (constantModelBoundedConstructible Λ X).ι hK).obj K)) := by
  let := closedSupport_lowerStarExact Λ i j hij
  intro closed support
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Z :=
    QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  have hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    rcases _hΛ with h | h
    · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr h⟩))
    · exact Or.inr (Or.inr (Or.inr h))
  have hbc (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
      constantModelBoundedConstructible Λ T ≤ localizingClosureProEtale Λ T := by
    have heq := (localizingClosure_ctf_equals_bc ℓ T Λ hcoeff).1.2.2.1
    intro K hK P _ hP
    apply hP K
    change (constantModelBoundedConstructible Λ T ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) K
    rwa [heq]
  have hpres : ∀ K, constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ Z
        ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K) := by
    rcases _hΛ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact support_preserved_of_coefficientIso e.symm i j hij
        ((rationalClosedSupportConstructible ℓ k p hpℓ i j hij).1 E)
    · exact support_preserved_of_coefficientIso e.symm i j hij
        (rationalClosedSupportConstructible ℓ k p hpℓ i j hij).2
  let hK : ∀ K : ConstantModelBoundedConstructible Λ X,
      localizingClosureProEtale Λ X K.obj := fun K ↦ hbc X K.obj K.property
  let hS : ∀ K : ConstantModelBoundedConstructible Λ X,
      localizingClosureProEtale Λ Z
        ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj) :=
    fun K ↦ hbc Z _ (hpres K.obj K.property)
  let PX := localizingClosureProEtale Λ X
  let PZ := localizingClosureProEtale Λ Z
  let T := PX.lift (constantModelBoundedConstructible Λ X).ι hK
  let S := PZ.lift ((constantModelBoundedConstructible Λ X).ι ⋙
    (formalClosedSupport Λ i j).rightDerivedFunctor) hS
  let L := (lowerStar Λ i).mapDerivedCategory
  let α (K : ConstantModelBoundedConstructible Λ X) (A : PZ.FullSubcategory) :
      (A ⟶ G.obj (T.obj K)) ≃ (L.obj A.obj ⟶ K.obj) :=
    ((adj.homEquiv A (T.obj K)).symm.trans PX.fullyFaithfulι.homEquiv).trans
      (Iso.homCongr (closed.app A) (Iso.refl _))
  let β (K : ConstantModelBoundedConstructible Λ X) (A : PZ.FullSubcategory) :
      (A ⟶ S.obj K) ≃ (L.obj A.obj ⟶ K.obj) :=
    PZ.fullyFaithfulι.homEquiv.trans (support.rightAdjoint.homEquiv A.obj K.obj).symm
  have hα (K : ConstantModelBoundedConstructible Λ X)
      {A B : PZ.FullSubcategory} (f : A ⟶ B) (g : B ⟶ G.obj (T.obj K)) :
      α K A (f ≫ g) = L.map (PZ.ι.map f) ≫ α K B g := by
    simp only [α, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply,
      Iso.homCongr_apply, Iso.refl_hom, Category.comp_id,
      Adjunction.homEquiv_naturality_left_symm, Functor.map_comp]
    simpa only [Functor.comp_map, Category.assoc, Iso.app_inv] using
      congrArg (fun t ↦ t ≫ PX.ι.map ((adj.homEquiv B (T.obj K)).symm g))
        (closed.inv.naturality f).symm
  have hβ (K : ConstantModelBoundedConstructible Λ X)
      {A B : PZ.FullSubcategory} (f : A ⟶ B) (g : B ⟶ S.obj K) :
      β K A (f ≫ g) = L.map (PZ.ι.map f) ≫ β K B g := by
    simp only [β, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply]
    rw [Functor.map_comp]
    exact support.rightAdjoint.homEquiv_naturality_left_symm _ _
  have hαq (K K' : ConstantModelBoundedConstructible Λ X) (q : K ⟶ K')
      (A : PZ.FullSubcategory) (g : A ⟶ G.obj (T.obj K)) :
      α K' A (g ≫ G.map (T.map q)) = α K A g ≫ q.hom := by
    simp only [α, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply,
      Iso.homCongr_apply, Iso.refl_hom, Category.comp_id,
      Adjunction.homEquiv_naturality_right_symm, Functor.map_comp, Category.assoc]
    rfl
  have hβq (K K' : ConstantModelBoundedConstructible Λ X) (q : K ⟶ K')
      (A : PZ.FullSubcategory) (g : A ⟶ S.obj K) :
      β K' A (g ≫ S.map q) = β K A g ≫ q.hom := by
    simp only [β, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply]
    rw [Functor.map_comp]
    exact support.rightAdjoint.homEquiv_naturality_right_symm _ _
  let θ (K : ConstantModelBoundedConstructible Λ X) : G.obj (T.obj K) ≅ S.obj K :=
    Yoneda.ext _ _
      (fun {A} g ↦ (β K A).symm (α K A g))
      (fun {A} g ↦ (α K A).symm (β K A g))
      (fun _ ↦ by simp) (fun _ ↦ by simp) (by
        intro A B f g
        apply (β K B).injective
        simp only [Equiv.apply_symm_apply, hβ, hα])
  have hθ (K : ConstantModelBoundedConstructible Λ X) :
      β K (G.obj (T.obj K)) (θ K).hom = α K (G.obj (T.obj K)) (𝟙 _) := by
    change β K _ ((β K _).symm (α K _ (𝟙 _))) = _
    exact Equiv.apply_symm_apply _ _
  let e : T ⋙ G ≅ S := NatIso.ofComponents θ (by
    intro K K' q
    apply (β K' (G.obj (T.obj K))).injective
    change β K' _ (G.map (T.map q) ≫ (θ K').hom) =
      β K' _ ((θ K).hom ≫ S.map q)
    rw [hβ, hθ, hβq, hθ, ← hαq K K' q _ (𝟙 _), ← hα K']
    simp only [Category.comp_id, Category.id_comp])
  refine ⟨hK, hS, e, ?_⟩
  intro K
  have hcompat := hθ K
  change L.map (PZ.ι.map (θ K).hom) ≫ support.rightAdjoint.counit.app K.obj =
    closed.inv.app (G.obj (T.obj K)) ≫
      PX.ι.map ((localizingLowerShriek Λ c.obj.obj h).map (𝟙 _) ≫
        adj.counit.app (T.obj K)) ≫ 𝟙 _ at hcompat
  rw [(localizingLowerShriek Λ c.obj.obj h).map_id, Category.id_comp,
    Category.comp_id] at hcompat
  exact hcompat

end AlgebraicGeometry.ProEtale.CondensedRing
