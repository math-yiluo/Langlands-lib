/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportSheaves
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Derived sections with closed support

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-formal-closed-support,
det-lem-formal-closed-support-derived.md, clauses (1)--(3); Stacks Project, Tag 079P
(blueprint: lemma-sections-support-closed-subscheme).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

private def adjunctionHomComplexIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive] (adj : L ⊣ R)
    (A : CochainComplex C ℤ) (I : CochainComplex D ℤ) :
    CochainComplex.HomComplex ((L.mapHomologicalComplex (.up ℤ)).obj A) I ≅
      CochainComplex.HomComplex A ((R.mapHomologicalComplex (.up ℤ)).obj I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (AddEquiv.piCongrRight fun t : CochainComplex.HomComplex.Triplet n ↦
      adj.homAddEquiv (A.X t.p) (I.X t.q)).toAddCommGrpIso)
    (by
      intro n m hnm
      apply AddCommGrpCat.ext
      intro a
      funext ⟨p, q, hpq⟩
      symm
      change adj.homEquiv _ _ (CochainComplex.HomComplex.δ n m a ⟨p, q, hpq⟩) =
        CochainComplex.HomComplex.δ (F := A)
          (G := (R.mapHomologicalComplex (.up ℤ)).obj I) n m
          (fun t ↦ adj.homEquiv (A.X t.p) (I.X t.q) (a t)) ⟨p, q, hpq⟩
      simp only [CochainComplex.HomComplex.δ, CochainComplex.HomComplex.Cochain.mk,
        CochainComplex.HomComplex.Cochain.v, Functor.mapHomologicalComplex_obj_d]
      rw [adj.homAddEquiv_add]
      congr 1
      · exact adj.homEquiv_naturality_right _ _
      · change (adj.homAddEquiv _ _) (_ • _) = _
        rw [Units.smul_def, map_zsmul, ← Units.smul_def]
        congr 1
        exact adj.homEquiv_naturality_left _ _)

private theorem epiUnitOfOtherLeftAdjoint
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R)
    (I : C) [Epi (adj'.unit.app I)] : Epi (adj.unit.app I) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj adj' I
  have hepi : Epi (adj.unit.app I ≫
      R.map ((Adjunction.leftAdjointUniq adj adj').hom.app I)) := by
    rw [h]
    infer_instance
  exact (epi_comp_iff_of_isIso (adj.unit.app I)
    (R.map ((Adjunction.leftAdjointUniq adj adj').hom.app I))).mp hepi

set_option backward.isDefEq.respectTransparency false in
private noncomputable def adjunctionUnitConeIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C]
    {L L' : C ⥤ D} {R : D ⥤ C} [L.Additive] [L'.Additive] [R.Additive]
    (adj : L ⊣ R) (adj' : L' ⊣ R) (I : CochainComplex C ℤ) :
    CochainComplex.mappingCone
      ((NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app I) ≅
    CochainComplex.mappingCone
      ((NatTrans.mapHomologicalComplex adj'.unit (.up ℤ)).app I) := by
  let c := Adjunction.leftAdjointUniq adj adj'
  let cI := (R.mapHomologicalComplex (.up ℤ)).mapIso
    ((NatIso.mapHomologicalComplex c (.up ℤ)).app I)
  let φ := (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app I
  let ψ := (NatTrans.mapHomologicalComplex adj'.unit (.up ℤ)).app I
  have hφψ : φ ≫ cI.hom = ψ := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact Adjunction.unit_leftAdjointUniq_hom_app adj adj' (I.X n)
  exact HomologicalComplex.homotopyCofiber.mapArrowIso φ ψ
    (fun n ↦ ⟨n - 1, by simp⟩)
    (Arrow.isoMk (Iso.refl I) cI ((Category.id_comp ψ).trans hφψ.symm))

set_option backward.isDefEq.respectTransparency false in
private theorem transportAdjunctionTriangle
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {L : D ⥤ C} {R R' : C ⥤ D} {U U' : C ⥤ E} {F : E ⥤ C}
    (adj : L ⊣ R) (adj' : L ⊣ R') (openAdj : U ⊣ F) (openAdj' : U' ⊣ F)
    (h : ∃ δ : U' ⋙ F ⟶ (R' ⋙ L) ⋙ shiftFunctor C (1 : ℤ),
      ∀ K : C, Triangle.mk (adj'.counit.app K) (openAdj'.unit.app K) (δ.app K) ∈
        distinguishedTriangles) :
    ∃ δ : U ⋙ F ⟶ (R ⋙ L) ⋙ shiftFunctor C (1 : ℤ),
      ∀ K : C, Triangle.mk (adj.counit.app K) (openAdj.unit.app K) (δ.app K) ∈
        distinguishedTriangles := by
  obtain ⟨δ, hδ⟩ := h
  let s := Adjunction.rightAdjointUniq adj adj'
  let t := Adjunction.leftAdjointUniq openAdj openAdj'
  let a := Functor.isoWhiskerRight s L
  let b := Functor.isoWhiskerRight t F
  let d := b.hom ≫ δ ≫ (Functor.isoWhiskerRight a (shiftFunctor C (1 : ℤ))).inv
  refine ⟨d, fun K ↦ ?_⟩
  refine isomorphic_distinguished _ (hδ K) _
    (Triangle.isoMk (Triangle.mk (adj.counit.app K) (openAdj.unit.app K) (d.app K))
      (Triangle.mk (adj'.counit.app K) (openAdj'.unit.app K) (δ.app K))
      (a.app K) (Iso.refl _) (b.app K) ?_ ?_ ?_)
  · change adj.counit.app K ≫ 𝟙 K =
      L.map ((Adjunction.rightAdjointUniq adj adj').hom.app K) ≫ adj'.counit.app K
    exact (Category.comp_id (adj.counit.app K)).trans
      (Adjunction.rightAdjointUniq_hom_app_counit adj adj' K).symm
  · change openAdj.unit.app K ≫ F.map
        ((Adjunction.leftAdjointUniq openAdj openAdj').hom.app K) =
      𝟙 K ≫ openAdj'.unit.app K
    rw [Category.id_comp]
    exact Adjunction.unit_leftAdjointUniq_hom_app openAdj openAdj' K
  · change (b.hom.app K ≫ δ.app K ≫
        (Functor.isoWhiskerRight a (shiftFunctor C (1 : ℤ))).inv.app K) ≫
      (shiftFunctor C (1 : ℤ)).map (a.hom.app K) = b.hom.app K ≫ δ.app K
    simp only [Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    simp

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Derived adjunction, global RHom, injective-unit surjectivity, and the natural support
triangle and fibre formula, using exactly the kernel functor of the sheaf-support node.
Source: blueprint main-20261015, lemma-sections-support-closed-subscheme, clauses (1)--(3)
(blueprint: lemma-sections-support-closed-subscheme).

Proof plan:
1. Finite type over the standing field gives a finite cover by Noetherian affine charts
   (lemma-sections-support-closed-subscheme). Every open is quasi-compact, hence j is
   quasi-compact and X is quasi-separated. These are consequences, not extra hypotheses.
2. The sheaf adjunction and exact i_* are lemma-sections-support-closed-subscheme--1.
   The exact-left-adjoint derived adjunction is adj.mapDerivedCategoryRightDerivedAdjunction.
   On a K-injective I the total right derived functor is computed by H(I), via
   Functor.rightDerivedFunctorObjQIso. The universal pair of lemma-sections-support-closed-subscheme
   agrees with this pair by its unit-compatible uniqueness. Apply the sheaf adjunction
   componentwise to the Hom complexes: naturality intertwines their two differentials.
   Both I and H(I) are K-injective, giving the displayed global RHom isomorphism.
3. Clause (3) of lemma-sections-support-closed-subscheme gives the epimorphic open unit
   on injectives, after the canonical coefficient-transport comparison. Equivalently,
   extend j_!j^*I -> I along the monomorphism j_!j^*I -> j_*j^*I by injectivity;
   open full faithfulness makes the extension a section of the unit.
4. Ring-sheaf modules are Grothendieck; lemma-sections-support-closed-subscheme resolves
   every unbounded complex by a K-injective complex with injective terms. Exact j_! is
   left adjoint to j^*, so j^* preserves K-injectives. The kernel identification and
   step 3 give a natural degreewise short exact sequence i_*H(I) -> I -> j_*j^*I.
5. Apply lemma-sections-support-closed-subscheme. Exact i_* computes its derived action.
   The termwise homotopy adjunction and the Hom bijection into K-injectives show that
   its second arrow is precisely the derived unit. Chain maps between resolutions
   represent all derived morphisms; additive functors preserve homotopies. Therefore
   the connecting arrows descend to the natural transformation delta in the statement.
6. Rotate the distinguished triangle and compare it with the cone triangle of this
   unit. TR3 and lemma-sections-support-closed-subscheme identify i_*RH(K) with its shifted cone.
   Apply exact i^* and its counit i^*i_* = id, giving the fibre formula. This uses the
   actual unit on I, not a functorial cone chosen in an arbitrary triangulated category.

The existential additive instance and ordinary adjunction only expose the structures
already asserted by the sheaf-support dependency. They impose no new assumptions.
The derived adjunction in (1) is the existing construction from this adjunction; its
counit is the first triangle arrow. The component formula specifies the natural global
RHom comparison. Every derived object admits the K-injective representative used in the
last clause, whose cone shifted by -1 is the fibre of the specified derived unit.
-/
theorem formal_closed_support_derived
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {X Z V : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (j : V ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (hij : Set.range j = (Set.range i)ᶜ) :
    ∃ (_ : (closedModuleSectionsWithSupport Λ i j).Additive),
      ∃ adj : lowerStar Λ i ⊣ closedModuleSectionsWithSupport Λ i j,
        letI : PreservesColimitsOfSize.{u + 1, u + 1} (lowerStar Λ i) :=
          adj.leftAdjoint_preservesColimits
        (∀ (A : CochainComplex (pulledBackModuleObjects Λ Z) ℤ)
          (I : CochainComplex (pulledBackModuleObjects Λ X) ℤ) [I.IsKInjective],
          ∃ e : CochainComplex.HomComplex
              (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I ≅
            CochainComplex.HomComplex A
              (((closedModuleSectionsWithSupport Λ i j).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I),
            ∀ (n : ℤ) (a : CochainComplex.HomComplex.Cochain
              (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I n)
              (p q : ℤ) (hpq : p + n = q),
              (e.hom.f n a) ⟨p, q, hpq⟩ =
                adj.homEquiv (A.X p) (I.X q) (a ⟨p, q, hpq⟩)) ∧
        (∀ (I : pulledBackModuleObjects Λ X) [Injective I],
          Epi ((upperStarLowerStarAdjunction Λ j).unit.app I)) ∧
        (∃ δ : (upperStar Λ j).mapDerivedCategory ⋙ (lowerStar Λ j).rightDerivedFunctor ⟶
            ((closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor ⋙
              (lowerStar Λ i).mapDerivedCategory) ⋙
                shiftFunctor (DerivedCategory (pulledBackModuleObjects Λ X)) (1 : ℤ),
          ∀ K : DerivedCategory (pulledBackModuleObjects Λ X),
            Triangle.mk (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app K)
              ((upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app
                K)
              (δ.app K) ∈ Pretriangulated.distinguishedTriangles) ∧
        (∀ (K : DerivedCategory (pulledBackModuleObjects Λ X))
          (I : CochainComplex (pulledBackModuleObjects Λ X) ℤ) [I.IsKInjective]
          (_e : K ≅ DerivedCategory.Q.obj I),
          Nonempty ((closedModuleSectionsWithSupport Λ i j).rightDerivedFunctor.obj K ≅
            (upperStar Λ i).mapDerivedCategory.obj
              (DerivedCategory.Q.obj
                ((shiftFunctor (CochainComplex (pulledBackModuleObjects Λ X) ℤ) (-1 : ℤ)).obj
                  (CochainComplex.mappingCone
                    ((NatTrans.mapHomologicalComplex (upperStarLowerStarAdjunction Λ j).unit
                      (ComplexShape.up ℤ)).app I)))))) := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : QuasiCompact j := inferInstance
  have hji : Set.range i.base = (Set.range j.base)ᶜ := by
    simp only [hij, compl_compl]
  obtain ⟨_, hlim, hcolim, ⟨adj⟩, _, _, hAdd, _⟩ :=
    formal_closed_support_sheaves Λ ℓ k hΛ i j hij
  let := hAdd
  let := hlim
  let := hcolim
  refine ⟨hAdd, adj, ?_, ?_, ?_, ?_⟩
  · intro A I _
    exact ⟨adjunctionHomComplexIso adj A I, fun _ _ _ _ _ ↦ rfl⟩
  · intro I _
    have := closedSupport_injective_unit_epi Λ i j hji I
    exact epiUnitOfOtherLeftAdjoint (upperStarLowerStarAdjunction Λ j)
      (supportPullbackAdjunction Λ j) I
  · exact transportAdjunctionTriangle adj.mapDerivedCategoryRightDerivedAdjunction
      (closedSupportDerivedAdjunction Λ i j hji)
      (upperStarLowerStarAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction
      (closedSupportOpenDerivedAdjunction Λ j) (closedSupport_triangle Λ i j hji)
  · intro K I _ e
    obtain ⟨eB⟩ := closedSupport_fiber Λ i j hji K I e
    let s := Adjunction.rightAdjointUniq adj.mapDerivedCategoryRightDerivedAdjunction
      (closedSupportDerivedAdjunction Λ i j hji)
    let t := Adjunction.leftAdjointUniq
      (upperStarLowerStarAdjunction Λ i).mapDerivedCategoryRightDerivedAdjunction
      (closedSupportOpenDerivedAdjunction Λ i)
    let ce := adjunctionUnitConeIso (supportPullbackAdjunction Λ j)
      (upperStarLowerStarAdjunction Λ j) I
    let qe := DerivedCategory.Q.mapIso
      ((shiftFunctor (CochainComplex (pulledBackModuleObjects Λ X) ℤ) (-1 : ℤ)).mapIso ce)
    exact ⟨s.app K ≪≫ eB ≪≫ (t.app _).symm ≪≫
      (upperStar Λ i).mapDerivedCategory.mapIso qe⟩

end AlgebraicGeometry.ProEtale.CondensedRing
