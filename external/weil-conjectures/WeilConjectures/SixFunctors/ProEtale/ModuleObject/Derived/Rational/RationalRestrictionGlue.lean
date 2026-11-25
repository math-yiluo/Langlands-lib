/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.SixFunctors.RestrictionLocal
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantStratifiedZariskiLocality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Gluing rational constructibility and restricting the exceptional adjunction

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-restriction/
sk-thm-restriction-glue.md and its proof (blueprint: theorem-f-shriek-ell-adic-coefficients).

The two restriction functors below retain the objects and maps of the supplied
compactification functor and its right adjoint. The theorem identifies their Hom
bijection with the original adjunction, including its naturality.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Restrict the actual compactification composite to bounded constructible objects.
The membership proof changes neither its objects nor its maps.
Source: blueprint sk-thm-restriction-glue, paragraph (2)
(blueprint: theorem-f-shriek-ell-adic-coefficients). -/
noncomputable def restrictionGlueLowerShriek (c : Compactification f)
    (hF : ∀ A, constantModelBoundedConstructible Λ X A →
      constantModelBoundedConstructible Λ Y
        ((rightDerivedLowerShriekOfCompactification Λ c).obj A)) :
    ConstantModelBoundedConstructible Λ X ⥤ ConstantModelBoundedConstructible Λ Y :=
  (constantModelBoundedConstructible Λ Y).lift
    ((constantModelBoundedConstructible Λ X).ι ⋙
      rightDerivedLowerShriekOfCompactification Λ c)
    (fun A ↦ hF A.obj A.property)

/-- Restrict the supplied right adjoint, using the full inclusion of Dbc into Loc(Dctf).
No new exceptional inverse image is chosen.
Source: blueprint sk-thm-restriction-glue, paragraph (2)
(blueprint: theorem-f-shriek-ell-adic-coefficients). -/
noncomputable def restrictionGlueUpperShriek
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (hY : constantModelBoundedConstructible Λ Y ≤ localizingClosureProEtale Λ Y)
    (hG : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
      constantModelBoundedConstructible Λ Y K.obj →
        constantModelBoundedConstructible Λ X (G.obj K).obj) :
    ConstantModelBoundedConstructible Λ Y ⥤ ConstantModelBoundedConstructible Λ X :=
  (constantModelBoundedConstructible Λ X).lift
    (ObjectProperty.ιOfLE hY ⋙ G ⋙ (localizingClosureProEtale Λ X).ι)
    (fun K ↦ hG ⟨K.obj, hY K.obj K.property⟩ K.property)

attribute [local irreducible] upperStar upperStarComp upperStarFromPoint

private noncomputable def pullbackCompObjIso {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C)
    (M : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1}) (condensedRingObj Λ C)) :
    (upperStar Λ (a ≫ b)).obj M ≅ (upperStar Λ a).obj ((upperStar Λ b).obj M) :=
  (upperStarComp Λ a b).app M

attribute [local irreducible] pullbackCompObjIso

private theorem pullbackConstructible {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsConstantModelConstructible Λ Y M) :
    IsConstantModelConstructible Λ X ((upperStar Λ g).obj M) := by
  classical
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  have hY : CompactSpace Y ∧ QuasiSeparatedSpace Y := ⟨inferInstance, inferInstance⟩
  simp only [IsConstantModelConstructible, ite_eq_left hX, ite_eq_left hY] at hM ⊢
  obtain ⟨S, hS⟩ := hM
  let T := S.pullback g
  refine ⟨T, fun i ↦ ?_⟩
  let q : T.domain i ⟶ S.domain i := pullback.fst (S.immersion i) g
  have comm : q ≫ S.immersion i = T.immersion i ≫ g := pullback.condition
  have h := pullback_finiteConstantLocalModel Λ q _ (hS i)
  let e := (pullbackCompObjIso Λ (T.immersion i) g M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (upperStar Λ f).obj M) comm.symm) ≪≫
    pullbackCompObjIso Λ q (S.immersion i) M
  obtain ⟨U, hU⟩ := h
  exact ⟨U, fun j ↦ by
    obtain ⟨P, hP, ⟨eP⟩⟩ := hU j
    exact ⟨P, hP, ⟨(upperStar Λ (U.f j)).mapIso e ≪≫ eP⟩⟩⟩

private theorem constructibleOpenGlue (X : Scheme.{u}) [IsNoetherian X]
    (I : Type w) [Finite I] (U : I → X.Opens) (hc : iSup U = ⊤)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∀ i, IsConstantModelConstructible Λ (U i).toScheme
      ((upperStar Λ (U i).ι).obj M)) : IsConstantModelConstructible Λ X M := by
  classical
  let := Fintype.ofFinite I
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hqs : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  simp only [IsConstantModelConstructible, ite_eq_left hqs]
  apply ((finiteConstantStratified_zariski_locality Λ X M).2.2 hqs.1 hqs.2).mpr
  intro W hW
  have : TopologicalSpace.NoetherianSpace W.toScheme :=
    W.ι.isOpenEmbedding.isInducing.noetherianSpace
  let V : Fin (Fintype.card I) → W.toScheme.Opens :=
    fun a ↦ W.ι ⁻¹ᵁ U (e a)
  apply (finiteConstantStratified_zariski_locality Λ X M).2.1 W hW.isCompact
    inferInstance (Fintype.card I) V
    (fun a ↦ TopologicalSpace.NoetherianSpace.isCompact _) ?_ ?_
  · apply Set.eq_univ_of_forall
    intro x
    have hx : W.ι x ∈ iSup U := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨e.symm i, by simpa [V] using hi⟩
  · intro a
    have : TopologicalSpace.NoetherianSpace (U (e a)).toScheme :=
      (U (e a)).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : TopologicalSpace.NoetherianSpace (V a).toScheme :=
      (V a).ι.isOpenEmbedding.isInducing.noetherianSpace
    let q : (V a).toScheme ⟶ (U (e a)).toScheme := W.ι ∣_ U (e a)
    have hp := pullbackConstructible Λ q _ (hM (e a))
    have hq : q ≫ (U (e a)).ι = (V a).ι ≫ W.ι := morphismRestrict_ι _ _
    have hlocalqs : CompactSpace (V a).toScheme ∧ QuasiSeparatedSpace (V a).toScheme :=
      ⟨inferInstance, inferInstance⟩
    have := (constantModelConstructibleFiniteTor_wellDefined Λ (V a).toScheme).1
    have h := ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ (V a).toScheme)
      ((pullbackCompObjIso Λ q (U (e a)).ι M).symm ≪≫
        eqToIso (congrArg (fun t ↦ (upperStar Λ t).obj M) hq)) hp
    simpa only [IsConstantModelConstructible, ite_eq_left hlocalqs] using h

private theorem zeroOpenGlue (X : Scheme.{u}) [IsNoetherian X]
    (I : Type w) [Finite I] (U : I → X.Opens) (hc : iSup U = ⊤)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∀ i, IsZero ((upperStar Λ (U i).ι).obj M)) : IsZero M := by
  apply isZero_of_isZero_X Λ
  apply (IsZero.iff_id_eq_zero _).mpr
  refine ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp
    (fun i ↦ (U i).ι) ?_ (𝟙 M.X) ?_
  · intro x
    have hx : x ∈ iSup U := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, by simpa using hi⟩
  · intro i
    have hz := ((Mod.forget _).map_isZero (hM i)).of_iso
      (upperStarObjXIso Λ (U i).ι M).symm
    exact hz.eq_of_src _ _

private theorem finiteOpenGlue (X : Scheme.{u}) [IsNoetherian X]
    (I : Type w) [Finite I] (U : I → X.Opens) (hcover : iSup U = ⊤)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hM : ∀ i, constantModelBoundedConstructible Λ (U i).toScheme
      ((upperStar Λ (U i).ι).mapDerivedCategory.obj M)) :
    constantModelBoundedConstructible Λ X M := by
  classical
  choose a ha using fun i ↦ (hM i).1.1
  choose b hb using fun i ↦ (hM i).1.2
  obtain ⟨r, hr⟩ := (Set.finite_range a).bddBelow
  obtain ⟨s, hs⟩ := (Set.finite_range b).bddAbove
  have hz (q : ℤ) (hq : q < r ∨ s < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj M) := by
    apply zeroOpenGlue Λ X I U hcover
    intro i
    have hi : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((upperStar Λ (U i).ι).mapDerivedCategory.obj M)) := by
      rcases hq with hq | hq
      · exact (DerivedCategory.isGE_iff _ (a i)).mp (ha i) q
          (hq.trans_le (hr (Set.mem_range_self i)))
      · exact (DerivedCategory.isLE_iff _ (b i)).mp (hb i) q
          ((hs (Set.mem_range_self i)).trans_lt hq)
    exact hi.of_iso (((upperStar Λ (U i).ι).mapDerivedCategoryHomologyFunctorIso q).app M)
  refine ⟨⟨⟨r, (DerivedCategory.isGE_iff M r).mpr (fun q hq ↦ hz q (Or.inl hq))⟩,
    ⟨s, (DerivedCategory.isLE_iff M s).mpr (fun q hq ↦ hz q (Or.inr hq))⟩⟩, fun q ↦ ?_⟩
  apply constructibleOpenGlue Λ X I U hcover
  intro i
  have := (constantModelConstructibleFiniteTor_wellDefined Λ (U i).toScheme).1
  exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ (U i).toScheme)
    (((upperStar Λ (U i).ι).mapDerivedCategoryHomologyFunctorIso q).app M).symm
    ((hM i).2 q)

private theorem pullbackBoundedConstructible {X Y : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g : X ⟶ Y)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    (hK : constantModelBoundedConstructible Λ Y K) :
    constantModelBoundedConstructible Λ X ((upperStar Λ g).mapDerivedCategory.obj K) := by
  have := (constantModelConstructibleFiniteTor_wellDefined Λ X).1
  refine ⟨(upperStar Λ g).bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
  exact ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
    (((upperStar Λ g).mapDerivedCategoryHomologyFunctorIso n).app K)
    (pullbackConstructible Λ g _ (hK.2 n))

private theorem auxiliaryAdjoint
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ℓ k)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ∃ (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
        ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
        (localizingClosureProEtale Λ X).FullSubcategory),
      Nonempty (localizingLowerShriek Λ c.obj.obj h ⊣ G) := by
  obtain ⟨h, hX, hY, hb⟩ := exists_localizingExceptionalAdjoint (hcd := hcd) Λ ℓ k f c hΛ
  let := hX
  let := hY
  obtain ⟨_, _, _, _, G, s, hs⟩ := hb
  let := s
  obtain ⟨_, _, adj, _⟩ := hs
  exact ⟨h, G, ⟨adj⟩⟩

/-- Finite open covers detect bounded constructibility, and the supplied exceptional
adjunction restricts to Dbc. The final equality says that its natural Hom bijection is
exactly the original one, after forgetting the full-subcategory membership proofs.
The arguments `h`, `G`, and `adj` name the functor and adjunction supplied by
theorem-existence-exceptional-inverse-image; no preservation of Dbc or inclusion in the localizing
closure is assumed. The coefficient identification is an isomorphism of condensed ring objects.
Source: blueprint sk-thm-restriction-glue, clauses (1)--(2)
(blueprint: theorem-f-shriek-ell-adic-coefficients).

Proof plan, following the six steps of the DAG:
1. The standing finite-type schemes are Noetherian (pqf-lem-locnoeth-lft,
   lem-weil-pbc-qcqs-over-affine). For the given rational coefficient
   det-def-localizing-closure-ctf-equals-bc gives Dctf = Dbc, hence Dbc lies in
   definition-localizing-subcategory. For Qbar use the finite-subextension-valued
   sk-def-sfb-qlbar-condensed ring.
2. Boundedness: forgetting to abelian sheaves (upperStarObjXIso), a module whose
   restrictions to a finite cover vanish is zero
   (lem-pod-finite-qc-proetale-abelian-detection). Exact restriction commutes with
   cohomology (def-sfb-exact-derived-cohomology-comparison); common bounds are taken
   over the finite ranges of local bounds, also for an empty index type.
3. Constructibility of each cohomology module: on each affine open W pull the cover
   back to W, pull back the local stratifications and finite constant models
   (lemma-constructible-pullback-stratification,
   new-unbounded-pullback-finite-constant-local-model) and assemble them with
   lem-sfb-constructible-zariski-locality, which also gives the global statement.
4. For K in Dbc, theorem-f-shriek-ell-adic-coefficients (with the projection and closed-immersion
   adjunctions supplied by theorem-existence-exceptional-inverse-image for
   proposition-construction-independence-rf-shriek) gives a finite affine chart cover where f^!K is
   bounded constructible; transport to the open ranges of the charts and apply clause (1).
5. proposition-construction-independence-rf-shriek preserves Dctf along the boundary
compactification
   (definition-compactification-refinement); step 1 identifies Dctf with Dbc.
6. The inclusions of Dbc into the localizing closures are fully faithful and the
   squares commute definitionally; CategoryTheory.Adjunction.restrictFullyFaithful
   gives the restricted adjunction with the original Hom equivalence.
-/
theorem rationalRestrictionGlue
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] E]
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
            (Profinite.padicSubfieldCondensedRing ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ℓ k)
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (h : ∀ A, localizingClosureProEtale Λ X A → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj A))
    (G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G) :
    (∀ (I : Type w) [Finite I] (U : I → X.Opens), iSup U = ⊤ →
      ∀ M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
        (∀ i : I, constantModelBoundedConstructible Λ (U i).toScheme
          (((upperStar Λ (U i).ι).mapDerivedCategory).obj M)) →
            constantModelBoundedConstructible Λ X M) ∧
    ∃ (hX : constantModelBoundedConstructible Λ X ≤ localizingClosureProEtale Λ X)
      (hY : constantModelBoundedConstructible Λ Y ≤ localizingClosureProEtale Λ Y)
      (hF : ∀ A, constantModelBoundedConstructible Λ X A →
        constantModelBoundedConstructible Λ Y
          ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj A))
      (hG : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
        constantModelBoundedConstructible Λ Y K.obj →
          constantModelBoundedConstructible Λ X (G.obj K).obj),
      ∃ adjbc : restrictionGlueLowerShriek Λ c.obj.obj hF ⊣
          restrictionGlueUpperShriek Λ G hY hG,
        ∀ (A : ConstantModelBoundedConstructible Λ X)
          (K : ConstantModelBoundedConstructible Λ Y)
          (t : (restrictionGlueLowerShriek Λ c.obj.obj hF).obj A ⟶ K),
          (adjbc.homEquiv A K t).hom =
            (adj.homEquiv ⟨A.obj, hX A.obj A.property⟩
              ⟨K.obj, hY K.obj K.property⟩ (ObjectProperty.homMk t.hom)).hom := by
  classical
  have : Fact (ringChar k).Prime := ⟨by rw [ringChar.eq k p]; exact Fact.out⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by rwa [ringChar.eq k p]⟩
  have noeth (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))] :
      IsNoetherian T := by
    have : IsLocallyNoetherian T :=
      LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
    have : CompactSpace T :=
      QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
    exact ⟨⟩
  have : IsNoetherian X := noeth X
  have : IsNoetherian Y := noeth Y
  have hcoeff :
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    rcases hΛ with h | h
    · exact Or.inl ⟨⟨E, inferInstance⟩, h⟩
    · exact Or.inr h
  have hadm : IsLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases hcoeff with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have htor (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
      (constantModelBoundedConstructible Λ T ⊓ _root_.DerivedCategory.finiteTorAmplitude _) =
        constantModelBoundedConstructible Λ T := by
    apply (localizingClosure_ctf_equals_bc ℓ T Λ ?_).1.2.2.1
    rcases hcoeff with ⟨E, hE⟩ | h
    · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr hE⟩))
    · exact Or.inr (Or.inr (Or.inr h))
  have hbc (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
      constantModelBoundedConstructible Λ T ≤ localizingClosureProEtale Λ T := by
    intro K hK P _ hP
    apply hP K
    change (constantModelBoundedConstructible Λ T ⊓ _root_.DerivedCategory.finiteTorAmplitude _) K
    rwa [htor T]
  have hX := hbc X
  have hY := hbc Y
  have hF : ∀ A, constantModelBoundedConstructible Λ X A →
      constantModelBoundedConstructible Λ Y
        ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj A) := by
    intro A hA
    apply ((compactification_localizing Λ ℓ k f c hadm).2.2.2 A ?_).1
    change (constantModelBoundedConstructible Λ X ⊓ _root_.DerivedCategory.finiteTorAmplitude _) A
    rwa [htor X]
  have hG : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
      constantModelBoundedConstructible Λ Y K.obj →
        constantModelBoundedConstructible Λ X (G.obj K).obj := by
    intro K hK
    obtain ⟨hloc, n, A, u, hA, hcov, hfac⟩ :=
      restrictionLocal Λ ℓ k hcoeff f c h G adj
    have hu : ∀ a, IsOpenImmersion (u a) := fun a ↦ (hA a).2
    let O : Fin n → X.Opens := fun a ↦ (u a).opensRange
    have hc : iSup O = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨a, y, hy⟩ := hcov x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨a, y, hy⟩
    apply finiteOpenGlue Λ X (Fin n) O hc
    intro a
    have : IsAffine (A a) := (hA a).1
    obtain ⟨V, v, hV, hv, d, i, hi, q, hqi, hq⟩ := hfac a
    have : IsAffine V := hV
    have : IsOpenImmersion v := hv
    have : IsClosedImmersion i := hi
    let : (A a).Over (Spec (.of k)) := ⟨u a ≫ (X ↘ Spec (.of k))⟩
    let : V.Over (Spec (.of k)) := ⟨v ≫ (Y ↘ Spec (.of k))⟩
    have : (u a).IsOver (Spec (.of k)) := ⟨rfl⟩
    have : v.IsOver (Spec (.of k)) := ⟨rfl⟩
    have : TopologicalSpace.NoetherianSpace (A a) :=
      (u a).isOpenEmbedding.isInducing.noetherianSpace
    have : TopologicalSpace.NoetherianSpace V :=
      v.isOpenEmbedding.isInducing.noetherianSpace
    have : IsSeparated (A a ↘ Spec (.of k)) :=
      (show IsSeparated (u a ≫ (X ↘ Spec (.of k))) from inferInstance)
    have : LocallyOfFiniteType (A a ↘ Spec (.of k)) :=
      (show LocallyOfFiniteType (u a ≫ (X ↘ Spec (.of k))) from inferInstance)
    have : QuasiCompact (A a ↘ Spec (.of k)) :=
      (show QuasiCompact (u a ≫ (X ↘ Spec (.of k))) from inferInstance)
    have : IsSeparated (V ↘ Spec (.of k)) :=
      (show IsSeparated (v ≫ (Y ↘ Spec (.of k))) from inferInstance)
    have : LocallyOfFiniteType (V ↘ Spec (.of k)) :=
      (show LocallyOfFiniteType (v ≫ (Y ↘ Spec (.of k))) from inferInstance)
    have : QuasiCompact (V ↘ Spec (.of k)) :=
      (show QuasiCompact (v ≫ (Y ↘ Spec (.of k))) from inferInstance)
    let P := AffineSpace (ULift.{u} (Fin d)) V
    let π : P ⟶ V := (AffineSpace.over (ULift.{u} (Fin d)) V).hom
    let : P.Over (Spec (.of k)) := ⟨π ≫ (V ↘ Spec (.of k))⟩
    have : π.IsOver (Spec (.of k)) := ⟨rfl⟩
    have : LocallyOfFinitePresentation π :=
      inferInstanceAs (LocallyOfFinitePresentation (AffineSpace (ULift.{u} (Fin d)) V ↘ V))
    have : LocallyOfFiniteType π := inferInstance
    have : IsSeparated (P ↘ Spec (.of k)) :=
      (show IsSeparated (π ≫ (V ↘ Spec (.of k))) from inferInstance)
    have : LocallyOfFiniteType (P ↘ Spec (.of k)) :=
      (show LocallyOfFiniteType (π ≫ (V ↘ Spec (.of k))) from inferInstance)
    have : QuasiCompact (P ↘ Spec (.of k)) :=
      (show QuasiCompact (π ≫ (V ↘ Spec (.of k))) from inferInstance)
    have : i.IsOver (Spec (.of k)) := ⟨by
      change i ≫ π ≫ v ≫ (Y ↘ Spec (.of k)) = u a ≫ (X ↘ Spec (.of k))
      rw [← Category.assoc, hqi, ← Category.assoc, hq, Category.assoc, comp_over]⟩
    let cp := AlgebraicGeometry.compactificationOverField k π
    let ci := AlgebraicGeometry.compactificationOverField k i
    obtain ⟨hp, Gp, ⟨adjp⟩⟩ := auxiliaryAdjoint (hcd := hcd) Λ ℓ k π cp hadm
    obtain ⟨hi', Gi, ⟨adji⟩⟩ := auxiliaryAdjoint (hcd := hcd) Λ ℓ k i ci hadm
    obtain ⟨huStar, _, _, hlocal⟩ :=
      hloc v (u a) hV (hA a).1 hv (hu a) d i hi q hqi hq
        cp hp Gp adjp ci hi' Gi adji
    obtain ⟨_, hlocal⟩ := hlocal K.obj hK
    have hlocal' : constantModelBoundedConstructible Λ (A a)
        ((upperStar Λ (u a)).mapDerivedCategory.obj (G.obj K).obj) := by
      have := (constantModelConstructibleFiniteTor_wellDefined Λ (A a)).2.1
      exact (constantModelBoundedConstructible Λ (A a)).prop_of_iso
        ((leftDerivedUpperStarIsoMapDerivedCategory Λ (u a)).app (G.obj K).obj) hlocal
    let e := (u a).isoOpensRange
    have : TopologicalSpace.NoetherianSpace (O a).toScheme :=
      (O a).ι.isOpenEmbedding.isInducing.noetherianSpace
    have hpull := pullbackBoundedConstructible Λ e.inv _ hlocal'
    have := (constantModelConstructibleFiniteTor_wellDefined Λ (O a).toScheme).2.1
    have heq : e.inv ≫ u a = (O a).ι :=
      (Iso.inv_comp_eq e).mpr (Scheme.Hom.isoOpensRange_hom_ι (u a)).symm
    let ec := (Functor.mapDerivedCategoryNatIso (upperStarComp Λ e.inv (u a)) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).app (G.obj K).obj
    exact (constantModelBoundedConstructible Λ (O a).toScheme).prop_of_iso
      (ec.symm ≪≫ eqToIso
        (congrArg (fun t ↦ (upperStar Λ t).mapDerivedCategory.obj (G.obj K).obj) heq)) hpull
  refine ⟨fun I _ U hc M hM ↦ finiteOpenGlue Λ X I U hc M hM,
    hX, hY, hF, hG, ?_⟩
  let iX := ObjectProperty.ιOfLE hX
  let iY := ObjectProperty.ιOfLE hY
  let comm1 : iX ⋙ localizingLowerShriek Λ c.obj.obj h ≅
      restrictionGlueLowerShriek Λ c.obj.obj hF ⋙ iY :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)
  let comm2 : iY ⋙ G ≅ restrictionGlueUpperShriek Λ G hY hG ⋙ iX :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp; rfl)
  let adjbc := adj.restrictFullyFaithful (ObjectProperty.fullyFaithfulιOfLE _)
    (ObjectProperty.fullyFaithfulιOfLE _) comm1 comm2
  refine ⟨adjbc, ?_⟩
  intro A K t
  simp only [adjbc, Adjunction.restrictFullyFaithful, comm1, comm2, iX, iY,
    ObjectProperty.fullyFaithfulιOfLE, ObjectProperty.ιOfLE]
  simp
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
