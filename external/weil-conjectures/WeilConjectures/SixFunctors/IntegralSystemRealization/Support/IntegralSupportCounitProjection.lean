/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralRealizationAssemblyData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Support.IntegralSupportTowerNormalization
import all WeilConjectures.SixFunctors.GeneratorReduction.ShortWordIntegralDomain

import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization

/-! # Counit-normalized projection of the primitive compact-support comparison

Source: blueprint fix-prop-coherence, strict-system expression realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem normalized_of_iso {V : Scheme.{u}}
    {A B : coefficientSequenceDerived.{u, u} l E V} (e : A ≅ B)
    (hA : IsNormalizedCoefficientSequence l E V A) :
    IsNormalizedCoefficientSequence l E V B := by
  intro m n h P
  let F := coefficientSequenceDerivedEvaluation.{u, u} l E V m
  let G := coefficientSequenceDerivedEvaluation.{u, u} l E V n
  let U := normalizedDVRRes l E V h
  let τ := coefficientSequenceDerivedTransition.{u, u} l E V h
  constructor
  · intro f g hfg
    apply (cancel_epi (G.map e.hom)).1
    apply (hA h P).1
    simp only [Functor.map_comp]
    change τ.app A ≫ (G ⋙ U).map e.hom ≫ U.map f =
      τ.app A ≫ (G ⋙ U).map e.hom ≫ U.map g
    change τ.app B ≫ U.map f = τ.app B ≫ U.map g at hfg
    rw [← τ.naturality_assoc e.hom, ← τ.naturality_assoc e.hom, hfg]
  · intro f
    obtain ⟨g, hg⟩ := (hA h P).2 (F.map e.hom ≫ f)
    refine ⟨G.map e.inv ≫ g, ?_⟩
    apply (cancel_epi (F.map e.hom)).1
    rw [← Category.assoc, τ.naturality e.hom]
    simp only [Functor.comp_map, Category.assoc, Functor.map_comp]
    rw [← U.map_comp_assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id, U.map_id,
      Category.id_comp]
    exact hg

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem bounds_of_iso {W : Scheme.{u}} {M N : System l E W}
    (e : M ≅ N) (hM : LevelBounds l E W M) : LevelBounds l E W N := by
  obtain ⟨a, b, c, d, hab, hcd, hlevels⟩ := hM
  refine ⟨a, b, c, d, hab, hcd, fun n ↦ ?_⟩
  let Rn := Padic.coefficientExtensionRing l E (n + 1)
  let A : proEtaleDerivedCategory W Rn :=
    (coefficientSequenceDerivedEvaluation l E W n).obj M
  let B : proEtaleDerivedCategory W Rn :=
    (coefficientSequenceDerivedEvaluation l E W n).obj N
  let q : A ≅ B := (coefficientSequenceDerivedEvaluation l E W n).mapIso e
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W) :=
    (proEtale_bounded_constructible_isTriangulated W Rn).1
  have hc : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W B :=
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W).prop_of_iso
      q (hlevels n).1
  have hb : proEtaleCohomologicalSupport (Y := W) (A := Rn) B ⊆ Set.Icc a b := by
    intro i hi
    apply (hlevels n).2.1
    intro hz
    exact hi (hz.of_iso ((DerivedCategory.homologyFunctor
      (proEtaleRingModules W (proEtaleConstantRing W Rn)) i).mapIso q).symm)
  have ht : HasProEtaleTorAmplitude W Rn B c d := by
    refine ⟨(hlevels n).2.2.1, ?_⟩
    rintro L P ⟨r⟩ f hf hP A i hi
    exact (hlevels n).2.2.2 L P ⟨r ≪≫ q.symm⟩ f hf hP A i hi
  exact ⟨hc, hb, ht⟩

private theorem origins_of_iso {W : Scheme.{u}} {M N : System l E W}
    (e : M ≅ N) (q : Origins l E W M) : Nonempty (Origins l E W N) := by
  refine ⟨{
    level := q.level
    origin := q.origin
    etaleTransition := q.etaleTransition
    fixedTransition := q.fixedTransition
    originSquare := q.originSquare
    evaluation := fun n ↦ q.evaluation n ≪≫
      (coefficientSequenceDerivedEvaluation.{u, u} l E W n).mapIso e
    transitionSquare := ?_ }⟩
  intro n
  erw [q.transitionSquare]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rw [(coefficientSequenceDerivedTransition.{u, u} l E W (Nat.le_succ n)).naturality_assoc e.hom]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem good_of_iso {W : Scheme.{u}} {M N : System l E W}
    (e : M ≅ N) (hM : Good l E W M) : Good l E W N := by
  refine ⟨normalized_of_iso l E e hM.1, bounds_of_iso l E e hM.2.1, ?_⟩
  obtain ⟨q⟩ := hM.2.2
  exact origins_of_iso l E e q

private theorem scalar_projection_composite (W : Scheme.{u}) (n : ℕ)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W) (N : System l E W)
    {Z : normalizedDVRDerived.{u, u} l E W n}
    (v : (coefficientSequenceDerivedEvaluation l E W n).obj N ⟶ Z) :
    ((coefficientFiniteAdjunction l E W n).homEquiv _ _).symm
      ((coefficientSequenceProjection l E W n).app N ≫
        (scalarReductionDerivedRestriction l E W n).map v) =
    (((S.reductionEvaluation n).inv.app ((coefficientSequenceLimit l E W).obj N)) ≫
      (coefficientSequenceDerivedEvaluation l E W n).map (S.adjunction.counit.app N)) ≫
        v := by
  apply ((coefficientFiniteAdjunction l E W n).homEquiv _ _).symm_apply_eq.mpr
  rw [Adjunction.homEquiv_naturality_right, S.counit_projection]
  rfl

private theorem open_normalized_transport (o : Operations l E) (a : AmbientModels l E o)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] [QuasiCompact j]
    (M : System l E U) (hM : Good l E U M)
    (hJ : Good l E V ((Operations.shriek l E o j).obj M))
    (H : Integral l E U) (b : (coefficientSequenceLimit.{u, u} l E U).obj M ≅ H)
    (rho : M ≅ (calculus l E U).reduction.obj H)
    (hn : (calculus l E U).reduction.map b.hom ≫ rho.inv =
      (calculus l E U).adjunction.counit.app M)
    [IsIso ((calculus l E V).adjunction.unit.app ((ringedOpen l E j).obj H))] :
    (a.openRealization j inferInstance M hM hJ).hom ≫ (ringedOpen l E j).map b.hom =
    (coefficientSequenceLimit.{u, u} l E V).map ((Operations.shriek l E o j).map rho.hom) ≫
      (coefficientSequenceLimit.{u, u} l E V).map ((a.realizationModel.openReduction l E j).app H) ≫
        inv ((calculus l E V).adjunction.unit.app ((ringedOpen l E j).obj H)) := by
  let L := coefficientSequenceLimit.{u, u} l E V
  let J := Operations.shriek l E o j
  let B : Integral l E U ⥤ Integral l E V := ringedOpen l E j
  let ε := (calculus l E U).adjunction.counit.app M
  let η := (calculus l E V).adjunction.unit
  have : IsIso ε :=
    ((purNormalizedReconstructionOfScheme l E U (calculus l E U)).1 M hM.1).2
  have hr : ε ≫ rho.hom = (calculus l E U).reduction.map b.hom := by
    change (calculus l E U).adjunction.counit.app M ≫ rho.hom = _
    rw [← hn, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (L.map (J.map ε))).1
  apply (cancel_mono (η.app (B.obj H))).1
  change (L.map (J.map ε) ≫ _ ≫ B.map b.hom) ≫ η.app (B.obj H) =
    (L.map (J.map ε) ≫ L.map (J.map rho.hom) ≫
      L.map ((a.realizationModel.openReduction l E j).app H) ≫
        inv (η.app (B.obj H))) ≫ η.app (B.obj H)
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  calc
    L.map (J.map ε) ≫ (a.openRealization j inferInstance M hM hJ).hom ≫
        B.map b.hom ≫ η.app (B.obj H) =
      L.map (J.map ε) ≫ (a.openRealization j inferInstance M hM hJ).hom ≫
        η.app (B.obj ((coefficientSequenceLimit.{u, u} l E U).obj M)) ≫
          ((calculus l E V).reduction ⋙ L).map (B.map b.hom) := by
      rw [← η.naturality]
      rfl
    _ = L.map ((a.realizationModel.openReduction l E j).app
        ((coefficientSequenceLimit.{u, u} l E U).obj M)) ≫
        ((calculus l E V).reduction ⋙ L).map (B.map b.hom) := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ ((calculus l E V).reduction ⋙ L).map (B.map b.hom))
          (a.openNormalization j M hM hJ)
    _ = L.map (J.map ((calculus l E U).reduction.map b.hom)) ≫
        L.map ((a.realizationModel.openReduction l E j).app H) := by
      simpa only [Functor.comp_map, ← Functor.map_comp] using
        congrArg L.map ((a.realizationModel.openReduction l E j).naturality b.hom).symm
    _ = L.map (J.map ε) ≫ L.map (J.map rho.hom) ≫
        L.map ((a.realizationModel.openReduction l E j).app H) := by
      rw [← hr, Functor.map_comp, Functor.map_comp, Category.assoc]

-- The final rewrite unfolds the scalar-reduction evaluation of the counit composite.
/-- Finite projection of the primitive open/proper realization, with an arbitrary
normalized input comparison substituted afterwards. There are no expression trees
or canonical-pair derivations in this assertion.

Source: blueprint fix-prop-coherence, compactification step of
lem-sf-integral-expression-coefficient-squares; Stacks 0941 and 0D6E.
(blueprint: lem-sf-integral-support-counit-projection).

Proof: transport Good through rho, retaining each origin evaluation and its actual
transition square. The general reconstruction lemma applied to b makes H integral
constructible. Specialize the compactification component of integralBasicRealization,
integralSupportTowerNormalization, to H. Its direct map d_H is the proper comparison,
the limit of openReduction, the inverse reconstruction unit, and the prescribed
compact-support realization. openNormalization, naturality of that unit and of
openReduction, and the supplied counit normalization identify L(SJ(rho)) followed by
d_H with the displayed primitive composite followed by that realization.
SfQcqsCompactSupportRealizationSpec identifies exactly the four finite transport
factors in the conclusion with scalar reduction of the realization and its recorded
finite reduction isomorphism. Apply the scalar-adjunction projection of d_H.
counit_projection and naturality of homEquiv evaluate its mate. The evaluated counit
is a natural transformation; its naturality at SJ(rho), followed by supportEvaluation
naturality at rho, gives the displayed right side. All actual quotient transitions
are retained. The same calculations apply to zero systems and empty opens. -/
theorem integralSupportCounitProjection (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (a : AmbientModels l E o)
    {U V : Over (Spec (CommRingCat.of D.k))}
    (f : U ⟶ V) (c : Compactification f.left)
    (hU : LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom)
    (hV : LocallyOfFiniteType V.hom ∧ QuasiCompact V.hom)
    (hf : IsSeparated f.left ∧ LocallyOfFiniteType f.left ∧ QuasiCompact f.left)
    (hq : QuasiCompact c.i)
    (M : System l E U.left) (hM : Good l E U.left M)
    (hJ : Good l E c.Z ((Operations.shriek l E o c.i).obj M))
    (hF : Good l E V.left
      ((Operations.push l E o c.g).obj ((Operations.shriek l E o c.i).obj M)))
    (H : Integral l E U.left)
    (b : (coefficientSequenceLimit l E U.left).obj M ≅ H)
    (rho : M ≅ (calculus l E U.left).reduction.obj H)
    (normalization : (calculus l E U.left).reduction.map b.hom ≫ rho.inv =
      (calculus l E U.left).adjunction.counit.app M) (n : ℕ) :
    (scalarReductionDerivedExtension l E V.left n).map
      ((a.realizationModel.push l E c.g).hom.app
          ((Operations.shriek l E o c.i).obj M) ≫
        (ringedPush l E c.g).map
          ((a.openRealization c.i hq M hM hJ).hom ≫
            (ringedOpen l E c.i).map b.hom)) ≫
      (PurCompactSupport.finiteReductionIso l E V.left n).inv.app
        ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj H) ≫
      (PurCompactSupport.comparison (PurCompactSupport.reduction l E (n + 1)
        (Nat.le_add_left 1 n)) c).app H ≫
      (PurCompactSupport.finiteImageIso l E n c).hom.app
        ((pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
          (Nat.le_add_left 1 n) U.left)).obj H) ≫
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
        ((PurCompactSupport.finiteReductionIso l E U.left n).hom.app H) =
    ((calculus l E V.left).reductionEvaluation n).inv.app
      ((coefficientSequenceLimit l E V.left).obj
        ((Operations.push l E o c.g).obj ((Operations.shriek l E o c.i).obj M))) ≫
      (coefficientSequenceDerivedEvaluation l E V.left n).map
        ((calculus l E V.left).adjunction.counit.app
          ((Operations.push l E o c.g).obj ((Operations.shriek l E o c.i).obj M))) ≫
      (supportEvaluation l E o c n).hom.app M ≫
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
        ((coefficientSequenceDerivedEvaluation l E U.left n).map rho.hom ≫
          ((calculus l E U.left).reductionEvaluation n).hom.app H) := by
  have : LocallyOfFiniteType (U.left ↘ Spec (.of D.k)) := hU.1
  have : QuasiCompact (U.left ↘ Spec (.of D.k)) := hU.2
  have : LocallyOfFiniteType (V.left ↘ Spec (.of D.k)) := hV.1
  have : QuasiCompact (V.left ↘ Spec (.of D.k)) := hV.2
  let := hf.1
  let := hf.2.1
  let := hf.2.2
  let := hq
  let L := coefficientSequenceLimit.{u, u} l E V.left
  let J := Operations.shriek l E o c.i
  let P := Operations.push l E o c.g
  let S := J ⋙ P
  let B : Integral l E U.left ⥤ Integral l E c.Z := ringedOpen l E c.i
  let Q : Integral l E c.Z ⥤ Integral l E V.left := ringedPush l E c.g
  let F := scalarReductionDerivedExtension.{u, u} l E V.left n
  let Vn := sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c
  have hH : sfIntegralConstructible l E U.left H := by
    obtain ⟨lo, hi, torLo, torHi, hlo, htor, hlevels⟩ := hM.2.1
    exact (GeneratorReduction.domain_of_realization l E U.left M lo hi torLo torHi
      ⟨hM.1, hM.2.2, hlo, htor, hlevels⟩ H b.symm).1
  let KH : (basicSupportDomain l E o c).FullSubcategory :=
    ⟨H, ⟨hH, good_of_iso l E rho hM, good_of_iso l E (S.mapIso rho) hF⟩,
      good_of_iso l E (J.mapIso rho) hJ⟩
  let hu := PurCompactSupport.coefficientPrimeUnit l D hl
  obtain ⟨T, eT, _, _, _, tower, d, hunit, hd, _, hproj⟩ :=
    integralSupportTowerNormalization l E D o a.realizationModel f.left hu c
  have := hunit KH
  have hop := open_normalized_transport l E o a c.i M hM hJ H b rho normalization
  let k := (a.realizationModel.push l E c.g).hom.app (J.obj M) ≫
    Q.map ((a.openRealization c.i hq M hM hJ).hom ≫ B.map b.hom)
  let τ := (sfQcqsCompactSupportRealization l E D.k hu c).hom.app
    ((basicSupportInput l E o c).obj KH)
  have hcompare : L.map (S.map rho.hom) ≫ d.hom.app KH = k ≫ τ := by
    erw [hd KH]
    change L.map (P.map (J.map rho.hom)) ≫
        (a.realizationModel.push l E c.g).hom.app (J.obj ((calculus l E U.left).reduction.obj H)) ≫
          Q.map _ ≫ τ = k ≫ τ
    erw [(a.realizationModel.push l E c.g).hom.naturality_assoc (J.map rho.hom)]
    change (a.realizationModel.push l E c.g).hom.app (J.obj M) ≫
        Q.map ((coefficientSequenceLimit.{u, u} l E c.Z).map (J.map rho.hom)) ≫
          Q.map _ ≫ τ = k ≫ τ
    simp only [← Q.map_comp_assoc]
    erw [← hop]
    exact (Category.assoc _ _ _).symm
  have hspec : SfQcqsCompactSupportRealizationSpec l E D.k hu c
      (sfQcqsCompactSupportRealization l E D.k hu c) :=
    (sfQcqsCompactSupportRealization_spec l E D.k hu c)
  let red := (sfCompactSupportFiniteReductionIso l D.k hu c E
    ((basicSupportInput l E o c).obj KH) n).hom
  let z := (PurCompactSupport.finiteReductionIso l E V.left n).inv.app
      ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj H) ≫
    (PurCompactSupport.comparison (PurCompactSupport.reduction l E (n + 1)
      (Nat.le_add_left 1 n)) c).app H ≫
    (PurCompactSupport.finiteImageIso l E n c).hom.app
      ((pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
        (Nat.le_add_left 1 n) U.left)).obj H) ≫
    Vn.map ((PurCompactSupport.finiteReductionIso l E U.left n).hom.app H)
  let μ : L ⋙ F ⟶ coefficientSequenceDerivedEvaluation l E V.left n :=
    Functor.whiskerLeft L ((calculus l E V.left).reductionEvaluation n).inv ≫
      Functor.whiskerRight (calculus l E V.left).adjunction.counit
        (coefficientSequenceDerivedEvaluation l E V.left n)
  let v := (supportEvaluation l E o c n).hom.app ((calculus l E U.left).reduction.obj H) ≫
    Vn.map (((calculus l E U.left).reductionEvaluation n).hom.app H)
  let w := (supportEvaluation l E o c n).hom.app M ≫
    Vn.map ((coefficientSequenceDerivedEvaluation l E U.left n).map rho.hom ≫
      ((calculus l E U.left).reductionEvaluation n).hom.app H)
  have hτ : F.map τ ≫ red = z := hspec ((basicSupportInput l E o c).obj KH) n
  have hp : F.map (d.hom.app KH) ≫ red = μ.app (S.obj _) ≫ v := by
    exact (hproj KH n).trans (scalar_projection_composite l E V.left n
      (calculus l E V.left) (S.obj _) v)
  have hμ : F.map (L.map (S.map rho.hom)) ≫ μ.app (S.obj _) =
      μ.app (S.obj M) ≫ (coefficientSequenceDerivedEvaluation l E V.left n).map
        (S.map rho.hom) := μ.naturality (S.map rho.hom)
  have hs : (coefficientSequenceDerivedEvaluation l E V.left n).map (S.map rho.hom) ≫
      (supportEvaluation l E o c n).hom.app _ =
    (supportEvaluation l E o c n).hom.app M ≫
      Vn.map ((coefficientSequenceDerivedEvaluation l E U.left n).map rho.hom) :=
    (supportEvaluation l E o c n).hom.naturality rho.hom
  have hv : (coefficientSequenceDerivedEvaluation l E V.left n).map (S.map rho.hom) ≫ v =
      w := by
    simpa only [v, w, Category.assoc, Functor.map_comp] using
      congrArg (fun q ↦ q ≫ Vn.map
        (((calculus l E U.left).reductionEvaluation n).hom.app H)) hs
  refine Eq.trans ?_ (Category.assoc _ _ w)
  change F.map k ≫ z = μ.app (S.obj M) ≫ w
  calc
    F.map k ≫ z = F.map k ≫ F.map τ ≫ red :=
      congrArg (fun q ↦ F.map k ≫ q) hτ.symm
    _ = F.map (L.map (S.map rho.hom)) ≫ F.map (d.hom.app KH) ≫ red := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun q ↦ F.map q ≫ red) hcompare.symm
    _ = F.map (L.map (S.map rho.hom)) ≫ μ.app (S.obj _) ≫ v := by rw [hp]
    _ = μ.app (S.obj M) ≫ w := by rw [← Category.assoc, hμ, Category.assoc, hv]

end WeilConjectures.IntegralSystemRealization
