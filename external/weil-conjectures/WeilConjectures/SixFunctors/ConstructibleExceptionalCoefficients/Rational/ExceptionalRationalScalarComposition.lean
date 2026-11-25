/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Rational.ExceptionalRationalStageLocalization
import WeilConjectures.SixFunctors.NormalizedRingCompactScalar.NormalizedRingCompactScalarCocycle
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Normalized.NormalizedScalarAssociatorLocalization
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.DeligneLaumon.CompactSupportNormalizedScalarIsomorphisms

/-! # Rational scalar composition using only the supplied ring and rational data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard Padic
universe u v w z
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private def integralInverse (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    (T : Scheme.{max u v}) [T.Over (Spec (.of D.k))]
    (E : FieldStage.{max u v} l) :
    sfIntegralConstructibleCategory l E.carrier T ⥤ C.{u, v} l Ω T (.integral E) := by
  let : ∀ x : T, Invertible (l : T.residueField x) :=
    sfCompactSupportScalarResidueUnit l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) T
  have h := (integral_residue_tor D l hl E.carrier T).2
  exact { obj K := ⟨K.obj, h ▸ K.property⟩
          map f := ObjectProperty.homMk f.hom }

private theorem rationalization_surjective
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    (T : Scheme.{max u v}) [T.Over (Spec (.of D.k))]
    (E : FieldStage.{max u v} l) (K : C.{u, v} l Ω T (.rational E)) :
    ∃ L : C.{u, v} l Ω T (.integral E), (rationalization.{u, v} l Ω E T).obj L = K := by
  exact ⟨(integralInverse l Ω D hl T E).obj K.obj, rfl⟩

private theorem fullSubcategory_functor_eq {A B : Type*} [Category A] [Category B]
    (P : ObjectProperty B) (F G : A ⥤ P.FullSubcategory) (h : F ⋙ P.ι = G ⋙ P.ι) :
    F = G := by
  have hobj (K : A) : F.obj K = G.obj K := by
    apply ObjectProperty.FullSubcategory.ext
    exact Functor.congr_obj h K
  refine CategoryTheory.Functor.ext hobj ?_
  intro K M f
  apply P.ι.map_injective
  simpa only [Functor.map_comp, eqToHom_map, Functor.comp_obj, Functor.comp_map] using
    Functor.congr_hom h f

private theorem scalar_localization_eq (E L : FieldStage.{max u v} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) (T : Scheme.{max u v})
    (S : C.{u, v} l Ω T (.integral E) ⥤ C.{u, v} l Ω T (.integral L))
    (hS : S ⋙ (finiteTorConstructibleIntegral l L.carrier T).ι =
      (finiteTorConstructibleIntegral l E.carrier T).ι ⋙
        integralScalarExtensionOfUniverses l E.carrier L.carrier i T) :
    rationalization.{u, v} l Ω E T ⋙ rationalScalar.{u, v} l Ω E L i T =
      S ⋙ rationalization.{u, v} l Ω L T := by
  let I := PurCompactSupport.finiteTorIntegralInclusion l E.carrier T
  let I' := PurCompactSupport.finiteTorIntegralInclusion l L.carrier T
  let U := sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
    E.carrier L.carrier i T
  have hI : S ⋙ I' = I ⋙ U :=
    fullSubcategory_functor_eq (sfIntegralConstructible l L.carrier T) _ _ hS
  apply Functor.hext
  · intro K
    exact (sfRationalScalarExtension_obj l E.carrier T 0
      (Fact.out : l.Prime).ne_zero L.carrier i _).trans
      (congrArg (sfRationalConstructibleLocalization l L.carrier T).obj
        (Functor.congr_obj hI.symm K))
  · intro K M f
    have ht := sfRationalScalarExtension_map_tmul l E.carrier T 0
      (Fact.out : l.Prime).ne_zero L.carrier i (I.obj K) (I.obj M) (I.map f) 1
    simp only [map_one] at ht
    exact ht.trans (Functor.hcongr_hom
      (congrArg (fun V ↦ V ⋙ sfRationalConstructibleLocalization l L.carrier T) hI.symm) f)

private theorem map_heq {A B : Type*} [Category A] [Category B]
    (G : A ⥤ B) {W X Y Z : A} (hW : W = Y) (hX : X = Z)
    {a : W ⟶ X} {b : Y ⟶ Z} (h : HEq a b) : HEq (G.map a) (G.map b) := by
  subst Y Z
  exact heq_of_eq (congrArg G.map (eq_of_heq h))

private theorem app_heq {A B : Type*} [Category A] [Category B]
    {G H : A ⥤ B} (η : G ⟶ H) {K M : A} (h : K = M) :
    HEq (η.app K) (η.app M) := by
  subst M
  rfl

private def normalizedScalar {s t : RingStage.{max u v} l}
    (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
    (T : Scheme.{max u v}) (S : Scalar.{u, v} l Ω a T) :
    NormalizedRingCompactScalar.Scalar.{u, v} l Ω a T :=
  ⟨S.functor, S.realization⟩

private def normalizedAssociator {s t r : RingStage.{max u v} l}
    {a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)}
    {b : PurCompactSupport.Change (t.coefficients l) (r.coefficients l)}
    {d : PurCompactSupport.Change (s.coefficients l) (r.coefficients l)}
    (h : ∀ T : Scheme.{max u v}, a.map T ≫ b.map T = d.map T)
    (T : Scheme.{max u v}) (A : Scalar.{u, v} l Ω a T)
    (B : Scalar.{u, v} l Ω b T) (D : Scalar.{u, v} l Ω d T)
    (α : ScalarComposition.{u, v} l Ω h T A B D) :
    NormalizedRingCompactScalar.Associator.{u, v} l Ω h T
      (normalizedScalar l Ω a T A) (normalizedScalar l Ω b T B)
      (normalizedScalar l Ω d T D) :=
  ⟨α.iso, α.normalized⟩

/--
The normalized rational left comparison satisfies scalar composition.
Source: exceptional inverse-image coefficient construction, rationalization paragraph;
the rational-arrow localization argument, Steps 1--4
(blueprint: lem-sf-ring-stage-rational-left-composition).

The proof first transports the integral compact-support scalar cocycle through the
specified localization. Every rational object is represented by an integral object with
the recorded finite Tor condition; the localized action formula then identifies each
localized integral arrow with the displayed rational scalar comparison. Functoriality of
localization transports the integral composition equation to the claimed equation.
-/
theorem ring_stage_rational_left_composition (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : RingStageAssembly.{u, v} l Ω D hl (f := f))
    (F : RationalStageAssembly.{u, v} l Ω D hl R) :
    ∀ (c : Compactification f) (E L M : FieldStage.{max u v} l)
      (i : E.carrier →ₐ[Padic l] L.carrier) (j : L.carrier →ₐ[Padic l] M.carrier)
      (K : C.{u, v} l Ω X (.rational E)),
      (rationalScalar.{u, v} l Ω L M j Y).map
          ((F.scalar c E L i).q.hom.app K) ≫
        (F.scalar c L M j).q.hom.app
          ((rationalScalar.{u, v} l Ω E L i X).obj K) ≫
        (F.operation c M).F.map
          ((sfRationalScalarComp l E.carrier L.carrier i X 0
            (Fact.out : l.Prime).ne_zero M.carrier j).hom.app K) =
      (sfRationalScalarComp l E.carrier L.carrier i Y 0
        (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
          ((F.operation c E).F.obj K) ≫
        (F.scalar c E M (j.comp i)).q.hom.app K := by
  classical
  intro c E L M i j K
  obtain ⟨K, rfl⟩ := rationalization_surjective l Ω D hl X E K
  let a := PurCompactSupport.completedChange l E.carrier L.carrier i
  let b := PurCompactSupport.completedChange l L.carrier M.carrier j
  let d := PurCompactSupport.completedChange l E.carrier M.carrier (j.comp i)
  let ha := Allowed.integral E L i
  let hb := Allowed.integral L M j
  let hd := Allowed.integral E M (j.comp i)
  let h := PurCompactSupport.completedMap_composition l E.carrier L.carrier i M.carrier j
  let AX := R.scalar (s := .integral E) (t := .integral L) a ha true
  let AY := R.scalar (s := .integral E) (t := .integral L) a ha false
  let BX := R.scalar (s := .integral L) (t := .integral M) b hb true
  let BY := R.scalar (s := .integral L) (t := .integral M) b hb false
  let DX := R.scalar (s := .integral E) (t := .integral M) d hd true
  let DY := R.scalar (s := .integral E) (t := .integral M) d hd false
  let αX := R.scalarComposition (s := .integral E) (t := .integral L) (r := .integral M)
    a b d h ha hb hd true
  let αY := R.scalarComposition (s := .integral E) (t := .integral L) (r := .integral M)
    a b d h ha hb hd false
  let qa := Scalar.counitQ l Ω AX AY
    (R.comparison c (s := .integral E) (t := .integral L) a ha)
  let qb := Scalar.counitQ l Ω BX BY
    (R.comparison c (s := .integral L) (t := .integral M) b hb)
  let qd := Scalar.counitQ l Ω DX DY
    (R.comparison c (s := .integral E) (t := .integral M) d hd)
  let sup (s : RingStage.{max u v} l) : NormalizedRingCompactScalar.Support l Ω c s :=
    ⟨(R.operation c s).F, R.left c s⟩
  have hi : BY.functor.map (qa.hom.app K) ≫ qb.hom.app (AX.functor.obj K) ≫
      (R.operation c (.integral M)).F.map (αX.iso.hom.app K) =
        αY.iso.hom.app ((R.operation c (.integral E)).F.obj K) ≫ qd.hom.app K :=
    (NormalizedRingCompactScalar.normalizedRingCompactScalarCocycle l Ω c D hl).composition
      (s := .integral E) (t := .integral L) (r := .integral M) a b d h
      (sup (.integral E)) (sup (.integral L)) (sup (.integral M))
      (normalizedScalar l Ω (s := .integral E) (t := .integral L) a X AX)
      (normalizedScalar l Ω (s := .integral E) (t := .integral L) a Y AY)
      (normalizedScalar l Ω (s := .integral L) (t := .integral M) b X BX)
      (normalizedScalar l Ω (s := .integral L) (t := .integral M) b Y BY)
      (normalizedScalar l Ω (s := .integral E) (t := .integral M) d X DX)
      (normalizedScalar l Ω (s := .integral E) (t := .integral M) d Y DY)
      qa qb qd
      (R.comparison_normalized c (s := .integral E) (t := .integral L) a ha)
      (R.comparison_normalized c (s := .integral L) (t := .integral M) b hb)
      (R.comparison_normalized c (s := .integral E) (t := .integral M) d hd)
      (normalizedAssociator l Ω (s := .integral E) (t := .integral L)
        (r := .integral M) h X AX BX DX αX)
      (normalizedAssociator l Ω (s := .integral E) (t := .integral L)
        (r := .integral M) h Y AY BY DY αY) K
  have sc (A B : FieldStage.{max u v} l) (i : A.carrier →ₐ[Padic l] B.carrier)
      (side : Bool) :
      rationalization.{u, v} l Ω A (endpoint X Y side) ⋙
          rationalScalar.{u, v} l Ω A B i (endpoint X Y side) =
        (R.scalar (s := .integral A) (t := .integral B)
          (PurCompactSupport.completedChange l A.carrier B.carrier i)
          (Allowed.integral A B i) side).functor ⋙
            rationalization.{u, v} l Ω B (endpoint X Y side) :=
    scalar_localization_eq l Ω A B i (endpoint X Y side) _
      (R.integralScalar_eq A B i side)
  have sx (A B : FieldStage.{max u v} l) (i : A.carrier →ₐ[Padic l] B.carrier)
      (N : C.{u, v} l Ω X (.integral A)) :
      (rationalScalar.{u, v} l Ω A B i X).obj
          ((rationalization.{u, v} l Ω A X).obj N) =
        (rationalization.{u, v} l Ω B X).obj
          ((R.scalar (s := .integral A) (t := .integral B)
            (PurCompactSupport.completedChange l A.carrier B.carrier i)
            (Allowed.integral A B i) true).functor.obj N) :=
    Functor.congr_obj (sc A B i true) N
  have sy (A B : FieldStage.{max u v} l) (i : A.carrier →ₐ[Padic l] B.carrier)
      (N : C.{u, v} l Ω Y (.integral A)) :
      (rationalScalar.{u, v} l Ω A B i Y).obj
          ((rationalization.{u, v} l Ω A Y).obj N) =
        (rationalization.{u, v} l Ω B Y).obj
          ((R.scalar (s := .integral A) (t := .integral B)
            (PurCompactSupport.completedChange l A.carrier B.carrier i)
            (Allowed.integral A B i) false).functor.obj N) :=
    Functor.congr_obj (sc A B i false) N
  have co (side : Bool) (N : C.{u, v} l Ω (endpoint X Y side) (.integral E)) :=
    normalized_scalar_associator_localization l Ω E L M i j (endpoint X Y side)
      (R.scalar (s := .integral E) (t := .integral L) a ha side)
      (R.scalar (s := .integral L) (t := .integral M) b hb side)
      (R.scalar (s := .integral E) (t := .integral M) d hd side)
      (R.integralScalar_eq E L i side) (R.integralScalar_eq L M j side)
      (R.integralScalar_eq E M (j.comp i) side)
      (R.integralScalar_normalized E L i side)
      (R.integralScalar_normalized L M j side)
      (R.integralScalar_normalized E M (j.comp i) side)
      (R.scalarComposition (s := .integral E) (t := .integral L) (r := .integral M)
        a b d h ha hb hd side) N
  let Q := rationalization.{u, v} l Ω M Y
  have hoa := (F.action c E).1 K
  have srcA :
      (rationalScalar.{u, v} l Ω E L i Y).obj
          ((F.operation c E).F.obj
            ((rationalization.{u, v} l Ω E X).obj K)) =
        (rationalization.{u, v} l Ω L Y).obj
          (AY.functor.obj ((R.operation c (.integral E)).F.obj K)) :=
    (congrArg (rationalScalar.{u, v} l Ω E L i Y).obj hoa).trans
      (sy E L i ((R.operation c (.integral E)).F.obj K))
  have tgtA :
      (F.operation c L).F.obj
          ((rationalScalar.{u, v} l Ω E L i X).obj
            ((rationalization.{u, v} l Ω E X).obj K)) =
        (rationalization.{u, v} l Ω L Y).obj
          ((R.operation c (.integral L)).F.obj (AX.functor.obj K)) :=
    (congrArg (F.operation c L).F.obj (sx E L i K)).trans
      ((F.action c L).1 (AX.functor.obj K))
  have scalarXX :
      (rationalScalar.{u, v} l Ω L M j X).obj
          ((rationalScalar.{u, v} l Ω E L i X).obj
            ((rationalization.{u, v} l Ω E X).obj K)) =
        (rationalization.{u, v} l Ω M X).obj (BX.functor.obj (AX.functor.obj K)) :=
    (congrArg (rationalScalar.{u, v} l Ω L M j X).obj (sx E L i K)).trans
      (sx L M j (AX.functor.obj K))
  have start :
      (rationalScalar.{u, v} l Ω L M j Y).obj
          ((rationalScalar.{u, v} l Ω E L i Y).obj
            ((F.operation c E).F.obj
              ((rationalization.{u, v} l Ω E X).obj K))) =
        Q.obj (BY.functor.obj (AY.functor.obj ((R.operation c (.integral E)).F.obj K))) :=
    (congrArg (rationalScalar.{u, v} l Ω L M j Y).obj srcA).trans
      (sy L M j (AY.functor.obj ((R.operation c (.integral E)).F.obj K)))
  have middle :
      (rationalScalar.{u, v} l Ω L M j Y).obj
          ((F.operation c L).F.obj
            ((rationalScalar.{u, v} l Ω E L i X).obj
              ((rationalization.{u, v} l Ω E X).obj K))) =
        Q.obj (BY.functor.obj ((R.operation c (.integral L)).F.obj (AX.functor.obj K))) :=
    (congrArg (rationalScalar.{u, v} l Ω L M j Y).obj tgtA).trans
      (sy L M j ((R.operation c (.integral L)).F.obj (AX.functor.obj K)))
  have afterB :
      (F.operation c M).F.obj
          ((rationalScalar.{u, v} l Ω L M j X).obj
            ((rationalScalar.{u, v} l Ω E L i X).obj
              ((rationalization.{u, v} l Ω E X).obj K))) =
        Q.obj ((R.operation c (.integral M)).F.obj (BX.functor.obj (AX.functor.obj K))) :=
    (congrArg (F.operation c M).F.obj scalarXX).trans
      ((F.action c M).1 (BX.functor.obj (AX.functor.obj K)))
  have finish :
      (F.operation c M).F.obj
          ((rationalScalar.{u, v} l Ω E M (j.comp i) X).obj
            ((rationalization.{u, v} l Ω E X).obj K)) =
        Q.obj ((R.operation c (.integral M)).F.obj (DX.functor.obj K)) :=
    (congrArg (F.operation c M).F.obj (sx E M (j.comp i) K)).trans
      ((F.action c M).1 (DX.functor.obj K))
  have direct :
      (rationalScalar.{u, v} l Ω E M (j.comp i) Y).obj
          ((F.operation c E).F.obj
            ((rationalization.{u, v} l Ω E X).obj K)) =
        Q.obj (DY.functor.obj ((R.operation c (.integral E)).F.obj K)) :=
    (congrArg (rationalScalar.{u, v} l Ω E M (j.comp i) Y).obj hoa).trans
      (sy E M (j.comp i) ((R.operation c (.integral E)).F.obj K))
  have hma : HEq
      ((rationalScalar.{u, v} l Ω L M j Y).map
        ((F.scalar c E L i).q.hom.app
          ((rationalization.{u, v} l Ω E X).obj K)))
      (Q.map (BY.functor.map (qa.hom.app K))) :=
    (map_heq _ srcA tgtA
      (F.scalar_normalized c E L i K)).trans
        (Functor.hcongr_hom (sc L M j false) (qa.hom.app K))
  have hmb : HEq
      ((F.scalar c L M j).q.hom.app
        ((rationalScalar.{u, v} l Ω E L i X).obj
          ((rationalization.{u, v} l Ω E X).obj K)))
      (Q.map (qb.hom.app (AX.functor.obj K))) :=
    (app_heq (F.scalar c L M j).q.hom (sx E L i K)).trans
      (F.scalar_normalized c L M j (AX.functor.obj K))
  have hmc : HEq
      ((F.operation c M).F.map
        ((sfRationalScalarComp l E.carrier L.carrier i X 0
          (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
            ((rationalization.{u, v} l Ω E X).obj K)))
      (Q.map ((R.operation c (.integral M)).F.map (αX.iso.hom.app K))) :=
    (map_heq _ scalarXX
      (sx E M (j.comp i) K) (co true K)).trans
        ((F.action c M).2 _ _ (αX.iso.hom.app K))
  have hmd : HEq
      ((sfRationalScalarComp l E.carrier L.carrier i Y 0
        (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
          ((F.operation c E).F.obj
            ((rationalization.{u, v} l Ω E X).obj K)))
      (Q.map (αY.iso.hom.app ((R.operation c (.integral E)).F.obj K))) :=
    (app_heq (sfRationalScalarComp l E.carrier L.carrier i Y 0
      (Fact.out : l.Prime).ne_zero M.carrier j).hom hoa).trans
        (co false ((R.operation c (.integral E)).F.obj K))
  have hleft : HEq
      ((rationalScalar.{u, v} l Ω L M j Y).map
          ((F.scalar c E L i).q.hom.app
            ((rationalization.{u, v} l Ω E X).obj K)) ≫
        (F.scalar c L M j).q.hom.app
          ((rationalScalar.{u, v} l Ω E L i X).obj
            ((rationalization.{u, v} l Ω E X).obj K)) ≫
        (F.operation c M).F.map
          ((sfRationalScalarComp l E.carrier L.carrier i X 0
            (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
              ((rationalization.{u, v} l Ω E X).obj K)))
      (Q.map (BY.functor.map (qa.hom.app K) ≫ qb.hom.app (AX.functor.obj K) ≫
        (R.operation c (.integral M)).F.map (αX.iso.hom.app K))) := by
    rw [Q.map_comp, Q.map_comp]
    exact CategoryTheory.heq_comp start middle finish hma
      (CategoryTheory.heq_comp middle afterB finish hmb hmc)
  have hright : HEq
      ((sfRationalScalarComp l E.carrier L.carrier i Y 0
        (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
          ((F.operation c E).F.obj
            ((rationalization.{u, v} l Ω E X).obj K)) ≫
        (F.scalar c E M (j.comp i)).q.hom.app
          ((rationalization.{u, v} l Ω E X).obj K))
      (Q.map (αY.iso.hom.app ((R.operation c (.integral E)).F.obj K) ≫ qd.hom.app K)) := by
    rw [Q.map_comp]
    exact CategoryTheory.heq_comp start direct finish
      hmd (F.scalar_normalized c E M (j.comp i) K)
  exact eq_of_heq (hleft.trans ((heq_of_eq (congrArg Q.map hi)).trans hright.symm))

end WeilConjectures.ConstructibleExceptionalCoefficients
