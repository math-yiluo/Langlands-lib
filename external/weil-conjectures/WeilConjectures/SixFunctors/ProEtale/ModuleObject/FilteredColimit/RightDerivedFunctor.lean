/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FilteredColimit.FunctorCategory

/-!
# Total right derived functors commute with filtered colimits of bounded below complexes

Let `G : C ⥤ D` be a left exact additive functor from a Grothendieck abelian category, and `J` a
small category such that colimits of shape `J` are exact in `C` and in `D` (e.g. `J` filtered),
and such that the classical right derived functors `RᵠG` commute with colimits of shape `J`.
Then for a diagram `F : J ⥤ CochainComplex C ℤ` of complexes uniformly bounded below and a
colimit cocone `c` of `F`, each cohomology functor of the total right derived functor `RG`
commutes with the colimit: `colim Hᵠ(RG(F j)) ≅ Hᵠ(RG(colim F))`
(`CategoryTheory.Functor.isColimit_mapCocone_Q_comp_rightDerivedFunctor_comp_homologyFunctor`).

Indeed, resolve `F` functorially by a diagram `I` of bounded below complexes of injectives
(`CategoryTheory.Functor.exists_quasiIso_injective_of_isStrictlyGE`). As colimits of shape `J` are
exact, `colim F ⟶ colim I` is a quasi-isomorphism; the colimits `colim_j I_j^n` are `G`-acyclic,
`RᵠG` commuting with colimits of shape `J`. So `RG` is computed termwise on the `I_j` and on
`colim I` (`CategoryTheory.Functor.isIso_rightDerivedFunctorUnitQ_of_isStrictlyGE`), and `G`
applied termwise, followed by cohomology, commutes with colimits of shape `J`.
-/

@[expose] public section

universe w

open CategoryTheory Limits

namespace CategoryTheory.Functor

/-- If the right derived functors of `G` commute with colimits of shape `J`, then a colimit of a
diagram of injective objects of shape `J` is `G`-acyclic. -/
lemma rightAcyclic_of_isColimit_of_injective {C D J : Type*} [Category* C] [Category* D]
    [Category* J] [Abelian C] [Abelian D] [HasInjectiveResolutions C] (G : C ⥤ D) [G.Additive]
    [∀ q, PreservesColimitsOfShape J (G.rightDerived q)] {I : J ⥤ C}
    (hI : ∀ j, Injective (I.obj j)) {c : Cocone I} (hc : IsColimit c) :
    G.rightAcyclic c.pt := fun q ↦
  (isColimitOfPreserves (G.rightDerived (q + 1)) hc).isZero_pt
    (Functor.isZero _ fun j ↦
      have := hI j
      G.isZero_rightDerived_obj_injective_succ q (I.obj j))

variable {C D : Type*} [Category.{w} C] [Category* D] [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w} C] [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions C]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]

/-- The unit `Q(G K) ⟶ RG(Q K)` of the right derived functor, as a natural transformation of
functors on cochain complexes. -/
@[simps]
noncomputable def rightDerivedFunctorUnitQNatTrans :
    G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor where
  app K := G.rightDerivedFunctorUnitQ K
  naturality _ _ f := G.rightDerivedFunctorUnitQ_naturality f

variable {J : Type w} [SmallCategory J] [HasExactColimitsOfShape J C]
  [HasColimitsOfShape J D] [HasExactColimitsOfShape J D]

/-- **The total right derived functor commutes with colimits of uniformly bounded below
complexes, on cohomology.** Let `J` be a small category such that colimits of shape `J` are exact
in `C` and `D`, and the right derived functors `RᵠG` commute with colimits of shape `J`. For a
diagram `F` of complexes strictly concentrated in degrees `≥ a` and a colimit cocone `c` of `F`,
the cocone `Hᵠ(RG(c))` is a colimit cocone. -/
theorem isColimit_mapCocone_Q_comp_rightDerivedFunctor_comp_homologyFunctor
    [∀ q, PreservesColimitsOfShape J (G.rightDerived q)]
    (F : J ⥤ CochainComplex C ℤ) (a : ℤ) [∀ j, (F.obj j).IsStrictlyGE a] {c : Cocone F}
    (hc : IsColimit c) (q : ℤ) :
    Nonempty (IsColimit ((DerivedCategory.Q ⋙ G.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor D q).mapCocone c)) := by
  obtain ⟨I, ι, hι, hIge, hIinj⟩ := exists_quasiIso_injective_of_isStrictlyGE F a
  let cI := colimit.cocone I
  have hcI : IsColimit cI := colimit.isColimit I
  -- the comparison `colim F ⟶ colim I` is a quasi-isomorphism
  let ι' : c.pt ⟶ cI.pt := hc.desc ((Cocone.precompose ι).obj cI)
  have hι' (j : J) : c.ι.app j ≫ ι' = ι.app j ≫ cI.ι.app j := hc.fac _ j
  have : QuasiIso ι' := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n
    have : ∀ j, IsIso ((Functor.whiskerRight ι H).app j) := fun j ↦
      (quasiIsoAt_iff_isIso_homologyMap (ι.app j) n).1 inferInstance
    have : IsIso (Functor.whiskerRight ι H) := NatIso.isIso_of_isIso_app _
    let f : H.mapCocone c ⟶ (Cocone.precompose (Functor.whiskerRight ι H)).obj (H.mapCocone cI) :=
      { hom := H.map ι'
        w j := (H.map_comp _ _).symm.trans ((congrArg H.map (hι' j)).trans (H.map_comp _ _)) }
    have : IsIso f := (IsColimit.hom_isIso (isColimitOfPreserves H hc)
      ((IsColimit.precomposeHomEquiv (asIso (Functor.whiskerRight ι H)) _).symm
        (isColimitOfPreserves H hcI)) f)
    exact (Cocone.forget _).map_isIso f
  -- `colim I` is a bounded below complex of `G`-acyclic objects
  have : cI.pt.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) i) hcI).isZero_pt
      (Functor.isZero _ fun j ↦ (I.obj j).isZero_of_isStrictlyGE a i hi)
  have hacyc (n : ℤ) : G.rightAcyclic (cI.pt.X n) :=
    G.rightAcyclic_of_isColimit_of_injective (I := I ⋙ HomologicalComplex.eval C _ n)
      (fun j ↦ hIinj j n)
      (isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) n) hcI)
  -- on bounded below complexes of `G`-acyclic objects, `RG` is computed termwise
  let Φ := DerivedCategory.Q ⋙ G.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D q
  let Ψ := G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⋙
    DerivedCategory.homologyFunctor D q
  let β : Ψ ⟶ Φ := Functor.whiskerRight (G.rightDerivedFunctorUnitQNatTrans)
    (DerivedCategory.homologyFunctor D q)
  have hβ (K : CochainComplex C ℤ) [K.IsStrictlyGE a] (hK : ∀ n, G.rightAcyclic (K.X n)) :
      IsIso (β.app K) := by
    have := G.isIso_rightDerivedFunctorUnitQ_of_isStrictlyGE K a hK
    exact Functor.map_isIso (DerivedCategory.homologyFunctor D q) (G.rightDerivedFunctorUnitQ K)
  have : PreservesColimitsOfShape J G :=
    preservesColimitsOfShape_of_natIso G.rightDerivedZeroIsoSelf
  have : PreservesColimitsOfShape J (G.mapHomologicalComplex (ComplexShape.up ℤ)) :=
    HomologicalComplex.preservesColimitsOfShape_of_eval _ fun i ↦
      preservesColimitsOfShape_of_natIso
        (NatIso.ofComponents (fun K ↦ Iso.refl _)
          (fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm) :
          HomologicalComplex.eval C (ComplexShape.up ℤ) i ⋙ G ≅
            G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
              HomologicalComplex.eval D (ComplexShape.up ℤ) i)
  have : PreservesColimitsOfShape J Ψ :=
    preservesColimitsOfShape_of_natIso (Functor.isoWhiskerLeft _
      (DerivedCategory.homologyFunctorFactors D q).symm)
  have hΦI : IsColimit (Φ.mapCocone cI) :=
    isColimitMapCoconeOfNatTrans' β cI (fun j ↦ hβ _ fun n ↦
      have := hIinj j n
      G.rightAcyclic_of_injective _)
      (hβ _ hacyc) (isColimitOfPreserves Ψ hcI)
  -- transport along the quasi-isomorphism `F ⟶ I`
  have : ∀ j, IsIso ((Functor.whiskerRight ι Φ).app j) := fun j ↦ by
    dsimp [Φ]
    infer_instance
  have : IsIso (Functor.whiskerRight ι Φ) := NatIso.isIso_of_isIso_app _
  have : IsIso (Φ.map ι') := by
    dsimp [Φ]
    infer_instance
  have hΦI' := (IsColimit.precomposeHomEquiv (asIso (Functor.whiskerRight ι Φ)) _).symm hΦI
  refine ⟨IsColimit.ofIsoColimit hΦI' (Cocone.ext (asIso (Φ.map ι')) fun j ↦ ?_).symm⟩
  exact (Φ.map_comp _ _).symm.trans ((congrArg Φ.map (hι' j)).trans (Φ.map_comp _ _))

end CategoryTheory.Functor
