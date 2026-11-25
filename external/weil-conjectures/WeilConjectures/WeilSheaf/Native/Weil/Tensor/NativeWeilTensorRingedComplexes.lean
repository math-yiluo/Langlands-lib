/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedBridge
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedUnderivedData
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedChainData
import WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedKFlatData

/-! # Normalized complex comparisons for an additive ringed presentation

Source: Stacks 06YS, 06YU, and steps 1--2 of native tensor transport.
These data precede the choice of any derived monoidal structure.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)
  (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
    ProEtaleWeilSheaf k₀ l X)
  [T.Additive] [∀ P, (T.obj P).Additive]
  [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
  (adj : T ⊣₂ ihomBifunctor k₀ l X)

/-- The reversed ringed tensor corresponding to the native right-parameter convention.
Source: Stacks 06YU (blueprint: lem-sf-native-weil-tensor-ringed-complexes). -/
abbrev nativeRingedTensorObj (P Q : ProEtaleWeilSheaf k₀ l X) :=
  (SheafOfModules.monoidalCategory b.R).tensorObj (b.native.functor.obj Q)
    (b.native.functor.obj P)

/-- The Koszul scalar on a ringed module morphism, with its hom group explicit.
Source: Stacks 06YU (blueprint: lem-sf-native-weil-tensor-ringed-complexes). -/
def nativeRingedTensorSign (p q : ℤ)
    {Y Z : RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R} (f : Y ⟶ Z) : Y ⟶ Z :=
  letI : AddCommGroup (Y ⟶ Z) :=
    @Preadditive.homGroup (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)
      _ inferInstance Y Z
  ZSMul.zsmul ((p * q).negOnePow : ℤ) f

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Normalized transport on complexes, without any derived tensor or forgetting comparison.
The total comparison includes the Koszul exchange because the native curried parameter
comes first, whereas the ringed tensor orders its actual tensor factors first.
Source: Stacks 06YS, 06YU
(blueprint: lem-sf-native-weil-tensor-ringed-complexes). -/
structure NativeWeilRingedTensorComplexes where
  /-- The unique comparison fixed by the two underived adjunctions. -/
  underived (P Q : ProEtaleWeilSheaf k₀ l X) :
    b.native.functor.obj ((T.obj P).obj Q) ≅ nativeRingedTensorObj b P Q
  /-- Evaluation fixes this comparison, including its scalar normalization. -/
  uncurry (P Q I : ProEtaleWeilSheaf k₀ l X)
      (f : Q ⟶ ((ihomBifunctor k₀ l X).obj (op P)).obj I) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients b.R
    letI := SheafOfModules.monoidalCategory b.R
    letI := SheafOfModules.symmetricCategory b.R
    (underived P Q).inv ≫
        b.native.functor.map (((adj.adj P).homEquiv Q I).symm f) =
      (β_ (b.native.functor.obj Q) (b.native.functor.obj P)).hom ≫
        ((SheafOfModules.tensorHomAdjunction b.R (b.native.functor.obj P)).homEquiv
          (b.native.functor.obj Q) (b.native.functor.obj I)).symm
            (b.native.functor.map f ≫ b.nativeHom.hom.app (op P, I))
  /-- Termwise transport followed by signed exchange of the two total directions. -/
  chain (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) :
    (b.native.functor.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q T) ≅
      (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).obj
        ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q,
          (b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
  /-- The total comparison is fixed on every tensor summand. -/
  summand (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n) :
    b.native.functor.map (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n hpq) ≫
        (chain P Q).hom.f n =
      nativeRingedTensorSign b p q ((underived (P.X p) (Q.X q)).hom ≫
        RingedForgetTensorTransposition.tensorSummand b.J b.R
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj Q)
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P) q p n hqp)
  /-- Naturality for arbitrary maps, before localization. -/
  naturality (P Q P' Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (f : P ⟶ P') (g : Q ⟶ Q') :
    (b.native.functor.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap f g T (.up ℤ)) ≫ (chain P' Q').hom =
      (chain P Q).hom ≫ (coefficientTotalTensor.{u + 1, u + 1, u + 1} b.J b.R).map
        (Prod.mkHom ((b.native.functor.mapHomologicalComplex (.up ℤ)).map g)
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).map f))
  /-- The equivalence preserves the full acyclic-test condition, without flat terms. -/
  flat (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X T P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := b.R)
      ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
  /-- All native K-flat complexes present the actual unbounded derived category. -/
  localization :
    ((ObjectProperty.ι (NativeTensorKFlat k₀ l X T)) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso (ProEtaleWeilSheaf k₀ l X) (.up ℤ)).inverseImage
        (ObjectProperty.ι (NativeTensorKFlat k₀ l X T)))

/-- An additive equivalence preserving the specified internal Hom gives the normalized
total tensor comparison and transports its K-flat localization.

Source: steps 1--2 of native tensor transport; Stacks 06YS, 06YU.
(blueprint: lem-sf-native-weil-tensor-ringed-complexes).

Proof: for each P, compose the equivalence's Hom bijections with nativeHom and
the sheaf tensor-Hom adjunction. Yoneda gives the unique underived comparison
whose inverse satisfies uncurry; the sheaf braiding puts Q before P. Naturality
of the parameter adjunction gives naturality in P as well as Q. Apply the additive
equivalence termwise, take the coproduct of these comparisons on each diagonal,
and exchange the two total directions with sign (-1)^(pq). This yields chain,
summand and naturality. The differential commutes because exchanging p and q
changes the two Koszul differentials by precisely that sign. The equivalence and
its inverse preserve all coproducts and preserve and reflect acyclicity. Every
ringed acyclic test is isomorphic to the image of a native test. Thus these chain
comparisons identify NativeTensorKFlat with ringed acyclic-test K-flatness. Ringed
K-flat resolutions transport through the equivalence of complexes. For localization,
first pass to homotopy categories: tensor respects chain homotopies, so contractible
complexes are K-flat, and K-flat complexes are closed under cones and shifts. Every
derived morphism is a roof. Replacing its middle complex by a K-flat resolution gives
a roof within the K-flat subcategory; the same replacement of a common refinement
proves injectivity on morphisms. Resolutions give essential surjectivity. These
comparisons and the homotopy quotient give the displayed localization of complexes.
No derived tensor, symmetry, closed structure or forgetful comparison is used.
All coproducts are countable; the proof applies to unbounded and zero complexes. -/
theorem native_weil_tensor_ringed_complexes :
    Nonempty (NativeWeilRingedTensorComplexes b T adj) := by
  obtain ⟨u⟩ := native_weil_tensor_ringed_underived_data b T adj
  obtain ⟨c⟩ := native_weil_tensor_ringed_chain_data b T adj u
    (nativeRingedTensorSign b) (by
      intro p q Y Z f
      rfl)
  obtain ⟨k⟩ := native_weil_tensor_ringed_kflat_data b T adj
  refine ⟨{ underived := u.underived
            uncurry := u.uncurry
            chain := c.chain
            summand := ?_
            naturality := c.naturality
            flat := k.flat
            localization := k.localization }⟩
  intro P Q p q n hpq hqp
  simpa only [nativeRingedTensorSign] using c.summand P Q p q n hpq hqp

end AlgebraicGeometry.ProEtaleWeilSheaf
