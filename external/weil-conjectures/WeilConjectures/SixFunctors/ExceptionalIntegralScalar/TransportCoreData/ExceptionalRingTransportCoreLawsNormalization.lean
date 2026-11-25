/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreData
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenSupportStepBounds
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenRealizationNaturality
/-! Proper/open normalization laws for exceptional integral transport.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26. (blueprint: lem-sf-exceptional-ring-transport-core-normalization-laws) -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients
structure TransportCoreNormalizationLaws
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left) where
  integralLeft_normalized (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    (sfIntegralConstructible l E.carrier Y).ι.map ((d.integralLeft E).hom.app K) =
      (left (.integral E)).hom.app K ≫
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K)
  inputGood (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    IntegralSystemRealization.Good l E.carrier X
      ((d.reconstruction E true).equivalence.functor.obj K).obj
  openGood (E : FieldStage.{u} l) (K : C.{u} l Ω X (.integral E)) :
    IntegralSystemRealization.Good l E.carrier c.Z
      ((IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i).obj
        ((d.reconstruction E true).equivalence.functor.obj K).obj)
  integral_system_normalized (E : FieldStage.{u} l)
      (K : C.{u} l Ω X (.integral E)) :
    (finiteTorConstructibleIntegral l E.carrier Y).ι.map
        ((d.realizeF E).inv.app K) ≫ (left (.integral E)).hom.app K ≍
      (IntegralSystemRealization.RealizationModel.push l E.carrier
          (d.realizations E).realizationModel c.g).hom.app
        ((IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i).obj
          ((d.reconstruction E true).equivalence.functor.obj K).obj) ≫
        (PurCompactSupport.push (PurCompactSupport.completed l E.carrier) c.g).map
          (((d.realizations E).openRealization c.i
              (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance)
              ((d.reconstruction E true).equivalence.functor.obj K).obj
              (inputGood E K) (openGood E K)).hom ≫
            (PurCompactSupport.openExtension (PurCompactSupport.completed l E.carrier)
              c.i).mapDerivedCategory.map
              ((eqToIso (congrArg
                  (fun H ↦ H.obj ((d.reconstruction E true).equivalence.functor.obj K))
                  (d.reconstruction E true).limit)).inv ≫
                (finiteTorConstructibleIntegral l E.carrier X).ι.map
                  ((d.reconstruction E true).equivalence.unitIso.inv.app K)))
/-- Normalized systems in the reconstruction category have the actual realization domain.
The levelwise finite-Tor predicate gives intrinsic constructibility, and the common
`IsGE` and `IsLE` bounds give a common cohomological support interval. Bounded
constructible descent lifts the actual system transitions to compatible etale origins.
Source: Zheng, Construction 4.1; Stacks 0941, and `openSupportStep_bounds`'s
bounded-origin construction.
(blueprint: lem-sf-exceptional-transport-sequence-good) -/
theorem sequenceProperty_good (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l)
    (T : Scheme.{u}) (N : coefficientSequenceDerived l E.carrier T)
    (hN : sequenceProperty l E T N) : IntegralSystemRealization.Good l E.carrier T N := by
  have hb : IntegralSystemRealization.LevelBounds l E.carrier T N := by
    obtain ⟨a, b, c, d, hab, hcd, h⟩ := hN.2
    refine ⟨a, b, c, d, hab, hcd, fun n ↦ ⟨(h n).1.1, ?_, (h n).2.2.2⟩⟩
    intro i hi
    constructor
    · exact le_of_not_gt (fun hlt ↦
        hi ((DerivedCategory.isGE_iff _ a).mp (h n).2.1 i hlt))
    · exact le_of_not_gt (fun hlt ↦
        hi ((DerivedCategory.isLE_iff _ b).mp (h n).2.2.1 i hlt))
  exact ⟨hN.1, hb, IntegralSystemRealization.origins_of_levelBounds l E.carrier T N hb⟩

section IntegralLeftNormalization
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f) (E : FieldStage.{u} l)
  (A : Operation.{u} l Ω X Y (.integral E))
  (r : LeftRealization.{u} l Ω c (.integral E) A)

/-- The integral comparison is the fully faithful lift of the given ambient left
realization followed by the proper/open compact-support realization.
Source: Zheng, Construction 5.25 and Proposition 5.26; the full-subcategory lift of
this specified natural isomorphism.
(blueprint: lem-sf-exceptional-integral-left-normalization-lift) -/
def normalizedIntegralLeft :
    A.F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y ≅
      PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier :=
  ((sfIntegralConstructible l E.carrier Y).fullyFaithfulι.whiskeringRight
    (finiteTorConstructibleIntegralCategory l E.carrier X)).preimageIso
      (r ≪≫ Functor.isoWhiskerLeft
        (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X)
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c))

/-- The fully faithful lift has exactly the prescribed ambient component.
Proof: the image of a preimage under a fully faithful functor is the original map;
apply this equality to each component of the ambient composite.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-integral-left-normalization-lift) -/
theorem normalizedIntegralLeft_hom (K : C.{u} l Ω X (.integral E)) :
    (sfIntegralConstructible l E.carrier Y).ι.map
        ((normalizedIntegralLeft l Ω D hl c E A r).hom.app K) =
      r.hom.app K ≫
        (sfQcqsCompactSupportRealization l E.carrier D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app
          ((PurCompactSupport.finiteTorIntegralInclusion l E.carrier X).obj K) := by
  let eambient :
      (A.F ⋙ PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y) ⋙
        (sfIntegralConstructible l E.carrier Y).ι ≅
      (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier) ⋙
        (sfIntegralConstructible l E.carrier Y).ι :=
    r ≪≫ Functor.isoWhiskerLeft
      (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X)
      (sfQcqsCompactSupportRealization l E.carrier D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c)
  exact congr_app
    (((sfIntegralConstructible l E.carrier Y).fullyFaithfulι.whiskeringRight
      (finiteTorConstructibleIntegralCategory l E.carrier X)).map_preimage eambient.hom) K

end IntegralLeftNormalization

section IntegralLeftObstruction
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
  (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
  (d : TransportCoreData l Ω D hl c operation left)

/-- Reconstruction inputs satisfy the full integral realization domain, independently
of the chosen comparison maps.
Proof: the equivalence lands in the sequence-property subcategory; apply
`sequenceProperty_good` to that object's property.
Source: Zheng, Construction 4.1 and Construction 5.25.
(blueprint: lem-sf-exceptional-transport-normalization-domains) -/
theorem TransportCoreData.inputGood (E : FieldStage.{u} l)
    (K : C.{u} l Ω X (.integral E)) :
    IntegralSystemRealization.Good l E.carrier X
      ((d.reconstruction E true).equivalence.functor.obj K).obj := by
  exact sequenceProperty_good l E X _
    ((d.reconstruction E true).equivalence.functor.obj K).property

/-- The intermediate extension-by-zero system satisfies the integral realization
 domain, independently of every freely chosen comparison.
Proof: the compactification ambient scheme is finite type over the original base
because its map to Y is proper. The open compactification arrow is quasi-compact.
Apply the open support theorem to the reconstructed Good input and the original
integral constructible object; retain its system conclusion.
Source: Zheng, Construction 5.25; Stacks 0941, 0GL1 and 0E8I.
(blueprint: lem-sf-exceptional-transport-normalization-domains) -/
theorem TransportCoreData.openGood (E : FieldStage.{u} l)
    (K : C.{u} l Ω X (.integral E)) :
    IntegralSystemRealization.Good l E.carrier c.Z
      ((IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i).obj
        ((d.reconstruction E true).equivalence.functor.obj K).obj) := by
  let U : Over (Spec (.of D.k)) := Over.mk (X ↘ Spec (.of D.k))
  let V : Over (Spec (.of D.k)) := Over.mk (c.g ≫ Y ↘ Spec (.of D.k))
  let j : U ⟶ V := Over.homMk c.i (by
    change c.i ≫ c.g ≫ Y ↘ Spec (.of D.k) = X ↘ Spec (.of D.k)
    rw [← Category.assoc, ← c.comm, comp_over f (Spec (.of D.k))])
  have : LocallyOfFiniteType U.hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of D.k)))
  have : QuasiCompact U.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of D.k)))
  have : LocallyOfFiniteType V.hom :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y ↘ Spec (.of D.k)))
  have : QuasiCompact V.hom :=
    inferInstanceAs (QuasiCompact (c.g ≫ Y ↘ Spec (.of D.k)))
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion c.i)
  have : QuasiCompact j.left :=
    IntegralSystemRealization.compactOpenQuasiCompact c inferInstance
  exact (IntegralSystemRealization.openSupportStep_bounds l E.carrier D hl (d.operations E)
    j _ (d.inputGood l Ω D hl c operation left E K) K.obj K.property.1).1

/-- Naturality of the supplied open realization on reconstruction inputs.
Proof: retain the ambient fields of the realization package and apply the
normalized open-realization naturality theorem to the reconstructed morphism.
Source: Zheng, Construction 5.25; normalized open-reconstruction unit and counit.
(blueprint: lem-sf-exceptional-transport-canonical-system-comparison) -/
theorem TransportCoreData.openRealization_naturality (E : FieldStage.{u} l)
    {K N : C.{u} l Ω X (.integral E)} (m : K ⟶ N) :
    (coefficientSequenceLimit l E.carrier c.Z).map
        ((IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i).map
          (((d.reconstruction E true).equivalence.functor ⋙
            (sequenceProperty l E X).ι).map m)) ≫
        ((d.realizations E).openRealization c.i
          (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance)
          ((d.reconstruction E true).equivalence.functor.obj N).obj
          (d.inputGood l Ω D hl c operation left E N)
          (d.openGood l Ω D hl c operation left E N)).hom =
      ((d.realizations E).openRealization c.i
        (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance)
        ((d.reconstruction E true).equivalence.functor.obj K).obj
        (d.inputGood l Ω D hl c operation left E K)
        (d.openGood l Ω D hl c operation left E K)).hom ≫
      (PurCompactSupport.openExtension (PurCompactSupport.completed l E.carrier)
        c.i).mapDerivedCategory.map
        ((coefficientSequenceLimit l E.carrier X).map
          (((d.reconstruction E true).equivalence.functor ⋙
            (sequenceProperty l E X).ι).map m)) := by
  let a : IntegralSystemRealization.AmbientModels l E.carrier (d.operations E) := {
    compositors := (d.realizations E).compositors
    openComparisons := (d.realizations E).openComparisons
    canonicalBridge := (d.realizations E).canonicalBridge
    properOpen := (d.realizations E).properOpen
    ringedTensorCoherence := (d.realizations E).ringedTensorCoherence
    realizationModel := (d.realizations E).realizationModel
    openRealization := (d.realizations E).openRealization
    openNormalization := (d.realizations E).openNormalization
    ringedModels := (d.realizations E).ringedModels
    ringedOpenComparisons := (d.realizations E).ringedOpenComparisons
    ringedProperOpen := (d.realizations E).ringedProperOpen }
  exact IntegralSystemRealization.integralOpenRealizationNaturality
    l E.carrier (d.operations E) a c.i
    (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance) _ _
    (d.inputGood l Ω D hl c operation left E K)
    (d.inputGood l Ω D hl c operation left E N)
    (d.openGood l Ω D hl c operation left E K)
    (d.openGood l Ω D hl c operation left E N) _

/-- The prescribed system realization, using the actual support equality and the
proper/open comparisons. All maps are specified; no existence witness is selected.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-transport-canonical-system-comparison) -/
def TransportCoreData.canonicalSystemRealization (E : FieldStage.{u} l)
    (hs : d.F E ⋙ (sequenceProperty l E Y).ι =
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g) :
    PurReconstruction.realized (d.reconstruction E true).equivalence
        (d.reconstruction E false).equivalence (d.F E) ⋙
        (finiteTorConstructibleIntegral l E.carrier Y).ι ≅
      (finiteTorConstructibleIntegral l E.carrier X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E.carrier) c := by
  let rX := d.reconstruction E true
  let rY := d.reconstruction E false
  let R := rX.equivalence.functor ⋙ (sequenceProperty l E X).ι
  let J := IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i
  let P := IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g
  let LX := coefficientSequenceLimit l E.carrier X
  let LZ := coefficientSequenceLimit l E.carrier c.Z
  let LY := coefficientSequenceLimit l E.carrier Y
  let j := (PurCompactSupport.openExtension (PurCompactSupport.completed l E.carrier)
    c.i).mapDerivedCategory
  let p := PurCompactSupport.push (PurCompactSupport.completed l E.carrier) c.g
  let eopen : R ⋙ J ⋙ LZ ≅ R ⋙ LX ⋙ j :=
    NatIso.ofComponents (fun K ↦ (d.realizations E).openRealization c.i
      (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance) (R.obj K)
      (d.inputGood l Ω D hl c operation left E K)
      (d.openGood l Ω D hl c operation left E K))
      (fun m ↦ d.openRealization_naturality l Ω D hl c operation left E m)
  let einput : R ⋙ LX ≅ (finiteTorConstructibleIntegral l E.carrier X).ι :=
    Functor.isoWhiskerLeft rX.equivalence.functor (eqToIso rX.limit).symm ≪≫
      Functor.isoWhiskerRight rX.equivalence.unitIso.symm
        (finiteTorConstructibleIntegral l E.carrier X).ι
  have hsource :
      PurReconstruction.realized rX.equivalence rY.equivalence (d.F E) ⋙
          (finiteTorConstructibleIntegral l E.carrier Y).ι = R ⋙ J ⋙ P ⋙ LY := by
    exact (congrArg (fun H ↦ (rX.equivalence.functor ⋙ d.F E) ⋙ H) rY.limit).trans
      (congrArg (fun H ↦ rX.equivalence.functor ⋙ H ⋙ LY) hs)
  exact eqToIso hsource ≪≫
    Functor.isoWhiskerLeft (R ⋙ J)
      (IntegralSystemRealization.RealizationModel.push l E.carrier
        (d.realizations E).realizationModel c.g) ≪≫
    Functor.isoWhiskerRight eopen p ≪≫
    Functor.isoWhiskerRight einput (j ⋙ p)

/-- Lift the specified system realization through the fully faithful integral
inclusion, fixing the comparison with the supplied integral operation.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-transport-canonical-system-comparison) -/
def TransportCoreData.canonicalRealizeF (E : FieldStage.{u} l)
    (hs : d.F E ⋙ (sequenceProperty l E Y).ι =
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g) :
    (operation (.integral E)).F ≅
      PurReconstruction.realized (d.reconstruction E true).equivalence
        (d.reconstruction E false).equivalence (d.F E) :=
  ((finiteTorConstructibleIntegral l E.carrier Y).fullyFaithfulι.whiskeringRight
    (finiteTorConstructibleIntegralCategory l E.carrier X)).preimageIso
      (left (.integral E) ≪≫
        (d.canonicalSystemRealization l Ω D hl c operation left E hs).symm)

/-- The canonical integral-system comparison satisfies the specified normalization.
Proof: mapping the fully faithful lift gives the prescribed composite. Cancel the
ambient left realization with its inverse. The source equality contributes only an
equality-transport map, which disappears under heterogeneous equality. The remaining
composite is exactly proper realization followed by the normalized open realization
and the reconstruction unit inverse.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-transport-canonical-system-comparison) -/
theorem TransportCoreData.canonicalRealizeF_normalized (E : FieldStage.{u} l)
    (hs : d.F E ⋙ (sequenceProperty l E Y).ι =
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g)
    (K : C.{u} l Ω X (.integral E)) :
    (finiteTorConstructibleIntegral l E.carrier Y).ι.map
        ((d.canonicalRealizeF l Ω D hl c operation left E hs).inv.app K) ≫
        (left (.integral E)).hom.app K ≍
      (IntegralSystemRealization.RealizationModel.push l E.carrier
          (d.realizations E).realizationModel c.g).hom.app
        ((IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i).obj
          ((d.reconstruction E true).equivalence.functor.obj K).obj) ≫
        (PurCompactSupport.push (PurCompactSupport.completed l E.carrier) c.g).map
          (((d.realizations E).openRealization c.i
              (IntegralSystemRealization.compactOpenQuasiCompact c inferInstance)
              ((d.reconstruction E true).equivalence.functor.obj K).obj
              (d.inputGood l Ω D hl c operation left E K)
              (d.openGood l Ω D hl c operation left E K)).hom ≫
            (PurCompactSupport.openExtension (PurCompactSupport.completed l E.carrier)
              c.i).mapDerivedCategory.map
              ((eqToIso (congrArg
                  (fun H ↦ H.obj ((d.reconstruction E true).equivalence.functor.obj K))
                  (d.reconstruction E true).limit)).inv ≫
                (finiteTorConstructibleIntegral l E.carrier X).ι.map
                  ((d.reconstruction E true).equivalence.unitIso.inv.app K))) := by
  let eambient := left (.integral E) ≪≫
    (d.canonicalSystemRealization l Ω D hl c operation left E hs).symm
  have hm := congr_app
    (((finiteTorConstructibleIntegral l E.carrier Y).fullyFaithfulι.whiskeringRight
      (finiteTorConstructibleIntegralCategory l E.carrier X)).map_preimage eambient.inv) K
  change (finiteTorConstructibleIntegral l E.carrier Y).ι.map
      ((d.canonicalRealizeF l Ω D hl c operation left E hs).inv.app K) =
    (d.canonicalSystemRealization l Ω D hl c operation left E hs).hom.app K ≫
      (left (.integral E)).inv.app K at hm
  rw [hm, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  dsimp only [TransportCoreData.canonicalSystemRealization]
  simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  refine (eqToHom_comp_heq _ _).trans ?_
  apply heq_of_eq
  simp only [Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
    NatTrans.comp_app, NatIso.ofComponents_hom_app, Iso.symm_hom,
    Functor.comp_map, Functor.map_comp, eqToIso.inv, eqToHom_app]
  rfl

/-- Fix both comparison maps by their prescribed proper/open constructions.
The support identity supplies the source transport for the system comparison;
all remaining transport fields are retained from the given data.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-transport-canonical-system-comparison) -/
def TransportCoreData.normalizeComparisons
    (hs : ∀ E : FieldStage.{u} l, d.F E ⋙ (sequenceProperty l E Y).ι =
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g) :
    TransportCoreData l Ω D hl c operation left :=
  { d with
    realizeF := fun E ↦ d.canonicalRealizeF l Ω D hl c operation left E (hs E)
    integralLeft := fun E ↦ normalizedIntegralLeft l Ω D hl c E
      (operation (.integral E)) (left (.integral E)) }

/-- The explicitly normalized comparisons satisfy the full normalization package.
Proof: fully faithful lifting proves the integral-left equation, the reconstructed
sequence and its open extension are Good, and canonicalRealizeF_normalized proves
the remaining system equation. No assertion about arbitrary comparison maps is used.
Source: Zheng, Construction 5.25 and Proposition 5.26.
(blueprint: lem-sf-exceptional-ring-transport-core-normalization-laws) -/
theorem TransportCoreData.normalizeComparisons_laws
    (hs : ∀ E : FieldStage.{u} l, d.F E ⋙ (sequenceProperty l E Y).ι =
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g) :
    Nonempty (TransportCoreNormalizationLaws l Ω D hl c operation left
      (d.normalizeComparisons l Ω D hl c operation left hs)) := by
  exact ⟨{
    integralLeft_normalized := fun E K ↦ normalizedIntegralLeft_hom l Ω D hl c E
      (operation (.integral E)) (left (.integral E)) K
    inputGood := d.inputGood l Ω D hl c operation left
    openGood := d.openGood l Ω D hl c operation left
    integral_system_normalized := fun E K ↦
      d.canonicalRealizeF_normalized l Ω D hl c operation left E (hs E) K }⟩

end IntegralLeftObstruction

/-- The prescribed proper/open comparison maps satisfy the normalization laws.
The support equation is needed to identify the system functor with proper push
following open extension. The conclusion concerns the explicitly normalized datum,
not arbitrary independently chosen comparisons.
Proof: construct the integral-left comparison by fully faithful lifting. Construct
the integral-system comparison from the support equality, proper realization, open
realization on Good systems, and the reconstruction unit. Lift this comparison
through the finite-Tor inclusion. Its image is the specified composite, so mapping
its inverse and canceling the ambient left realization gives the fourth law.
The reconstructed input and its open extension are Good by the bounded-system and
open-support theorems.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26. (blueprint: lem-sf-exceptional-ring-transport-core-normalization-laws) -/
theorem exists_exceptional_transport_core_normalization_laws
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left)
    (hs : ∀ E : FieldStage.{u} l, d.F E ⋙ (sequenceProperty l E Y).ι =
      (sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g) :
    Nonempty (TransportCoreNormalizationLaws l Ω D hl c operation left
      (d.normalizeComparisons l Ω D hl c operation left hs)) := by
  exact d.normalizeComparisons_laws l Ω D hl c operation left hs
end WeilConjectures.ExceptionalIntegralScalar
