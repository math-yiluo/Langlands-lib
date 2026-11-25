/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealization
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationTensor
import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalenceFunctoriality

/-!
# Pullback and condensed realization of native K-flat complexes

- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_upperStar_obj`: the pullback `g^*` of
  pro-étale Weil sheaves along any morphism `g` of `k₀`-schemes sends native K-flat complexes to
  native K-flat complexes (Stacks 06YW).
- `AlgebraicGeometry.ProEtaleWeilSheaf.kFlat_condensedRealization`: the condensed realization of
  a native K-flat complex is K-flat.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Pullback of pro-étale Weil sheaves along any morphism `g : Z ⟶ Y` of `k₀`-schemes preserves
native K-flat complexes (Stacks 06YW). -/
theorem nativeIsKFlat_upperStar_obj {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ) (hP : NativeIsKFlat k₀ l Y P) :
    NativeIsKFlat k₀ l Z (((upperStar k₀ l g).mapHomologicalComplex (.up ℤ)).obj P) :=
  nativeIsKFlat_mapHomologicalComplex_obj_of_iso k₀ l (upperStar k₀ l g) _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso
        (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l g _)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ProEtale.adicUpperStarCompCondensedModIso l
        (Scheme.Hom.geometricFiberMap g (comp_over g _))) ≪≫
      (Functor.associator _ _ _).symm) P
    (ProEtale.CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj
      (Profinite.padicAlgClRingObj l) (Scheme.Hom.geometricFiberMap g (comp_over g _))
      (kFlat_condensedRealization_mapHomologicalComplex k₀ l Y P hP))

/-- The condensed realization of a native K-flat complex of pro-étale Weil sheaves is K-flat. -/
theorem kFlat_condensedRealization (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) (hP : NativeIsKFlat k₀ l X P) :
    (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((condensedRealization k₀ l X).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (HomotopyCategory.kFlat_quotient_obj_iff _).2
    (kFlat_condensedRealization_mapHomologicalComplex k₀ l X P hP)

end AlgebraicGeometry.ProEtaleWeilSheaf
