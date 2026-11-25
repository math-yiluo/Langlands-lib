/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.Points
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction
public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Stalks, trace functions and weights of Weil sheaves and Weil complexes

Let `F` be a Weil sheaf on a `k₀`-scheme `X`: a constructible `ℓ`-adic pro-étale sheaf on the
geometric fiber `X̄ = X ×_{k₀} k̄` with an isomorphism `φ : Fr^* F ≅ F`, where `Fr = 𝟙 × σ` is the
geometric Galois Frobenius of `X̄` and `σ` the automorphism of `Spec k̄` induced by the
geometric Frobenius of `k̄`. This file constructs the geometric stalks of `F` with their local
Frobenius, the trace function, the support and the global sections of `F`, and phrases
punctual purity, upper weight bounds and reality on the stalks.

## The local Frobenius

For a geometric point `s : Spec k̄ ⟶ X̄`, the iterated Weil structure
`φ_m : (Frᵐ)^* F ≅ F` (`AlgebraicGeometry.WeilSheaf.frobeniusPowIso`) induces
`F_{s ≫ Frᵐ} ≅ ((Frᵐ)^* F)_s ≅ F_s`. The point `s ≫ Frᵐ` is not `s` itself: its second
component `Spec k̄ ⟶ Spec k̄` is `σᵐ` instead of the identity. If `s` lies over a point with
values in a field with `qᵐ` elements, then `s ≫ Frᵐ = σᵐ ≫ s`
(`AlgebraicGeometry.Scheme.Hom.geometricFiberPoint_comp_geometricGaloisFrobenius_pow`), and
the stalk at the reparametrisation `σᵐ ≫ s` of `s` is canonically the stalk at `s`, pullback
along the automorphism `σᵐ` of `Spec k̄` not changing global sections
(`AlgebraicGeometry.ProEtale.globalSectionsUpperStarIso`). The composite

`F_s ≅ F_{σᵐ ≫ s} = F_{s ≫ Frᵐ} ≅ F_s`

is the local Frobenius `F_x^{(m)}` on the stalk, `AlgebraicGeometry.WeilSheaf.stalkAt`.

At a closed point `x` of `X` with residue field `κ(x)` of degree `e_x` over `k₀`, the
geometric point is `Spec k̄ ⟶ Spec κ(x) ⟶ X` for a `k₀`-embedding `κ(x) ↪ k̄`, chosen by
`IsAlgClosed.lift`, lifted to `X̄`; at an `𝔽_{qⁿ}`-rational point the same construction is
made with an embedding `𝔽_{qⁿ} ↪ k̄`. The choice of the point does not change the
characteristic polynomial of the Frobenius
(`AlgebraicGeometry.WeilSheaf.charpoly_frobeniusEnd_stalkAt_of_dvd`), so that the trace
function is computed by the local Frobenius at the closed points,
`F_y^{(n)} = F_x^{n / e_x}`
(`AlgebraicGeometry.WeilSheaf.traceFunction_eq_trace_frobeniusEnd_stalk_pow`).

## Main declarations

- `AlgebraicGeometry.WeilSheaf.stalkAt`: the stalk at a geometric point fixed by `Frᵐ`, up to
  reparametrisation, with its Frobenius.
- `AlgebraicGeometry.WeilSheaf.stalk`: the geometric stalk at a closed point with its local
  geometric Frobenius `Fₓ`.
- `AlgebraicGeometry.WeilSheaf.support`: the closed points with nonzero stalk.
- `AlgebraicGeometry.WeilSheaf.traceFunction`: the trace function `t_{F,n}`.
- `AlgebraicGeometry.WeilComplex.traceFunction`: the trace function `t_K` of a Weil complex, the
  alternating sum of the trace functions of its cohomology sheaves.
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight`,
  `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost` and `AlgebraicGeometry.WeilSheaf.IsReal`: the
  weight conditions and the reality condition.
- `AlgebraicGeometry.WeilSheaf.globalSections`: the global sections `Γ(X̄, F)` with the
  Frobenius induced by `φ`, and `AlgebraicGeometry.WeilSheaf.globalSectionsToStalkObj`, their
  restriction to a stalk.

## Main statements

- `AlgebraicGeometry.WeilSheaf.charpoly_frobeniusEnd_stalkAt_of_dvd`: the characteristic
  polynomial of the local Frobenius does not depend on the geometric point.
- `AlgebraicGeometry.WeilSheaf.traceFunction_eq_trace_frobeniusEnd_stalk_pow`: the trace
  function at an `𝔽_{qⁿ}`-point over a closed point `x` is `Tr(Fₓ^{n / e_x})`.
- `AlgebraicGeometry.WeilComplex.traceFunction_eq_sum`: the alternating sum defining the trace
  function of a Weil complex is finite.
- `AlgebraicGeometry.WeilSheaf.globalSectionsToStalkObj_frobenius`: restriction of global
  sections to a stalk intertwines the two Frobenii.
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.upperStar` (in
  `WeilConjectures.WeilSheaf.StalkUpperStar`): pullback preserves punctual purity (blueprint:
  `proposition-weights-under-usual-operations--7`).

## Implementation notes

The stalk at a geometric point `s : Spec k̄ ⟶ X̄` is `Γ(Spec k̄, s^* F)`, the global sections
of the pro-étale pullback. A module over `ULift ℚ̄_ℓ` is made a `ℚ̄_ℓ`-module by restriction of
scalars (`AlgebraicGeometry.WeilCoefficients.toModuleCat`).

Both detection statements rest on a finite stratification of `X̄` into locally closed strata
on which `F` is lisse. Pullbacks to the strata detect sections
(`AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero`), and on a stratum the
section, a column of continuous `ℓ`-adic functions on a trivialising pro-étale cover, vanishes as
soon as it vanishes at a geometric point over every irreducible component
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_globalSectionsToUpperStar_eq_zero`);
a nonzero lisse sheaf has nonzero stalks over some closed point
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_isClosed_nontrivial_globalSections_upperStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite ZeroObject

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]
variable {k₀ : Type u} [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
variable (F : WeilSheaf k₀ l X)

section GeometricStalk

/-- The stalk `F_s` of the underlying `ℓ`-adic sheaf of a Weil sheaf at a geometric point
`s : Spec k̄ ⟶ X̄`: the global sections `Γ(Spec k̄, s^* F)` of its pro-étale pullback. Every
pro-étale cover of `Spec k̄` splits, so global sections on `Spec k̄` are exact, and for the
constant sheaf `ℚ̄_ℓ` they are `ℚ̄_ℓ`. -/
noncomputable def stalkObj
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    WeilCoefficients.{u} l :=
  (Sheaf.Γ _ _).obj ((s)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X)

/-- The stalks of a Weil sheaf are finite-dimensional: the pullback of the underlying sheaf to
`Spec k̄` is constructible, hence a finite sum of copies of `ℚ̄_ℓ`, whose global sections are
`ℚ̄_ℓ` (`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.finiteDimensional_globalSections`).
-/
theorem finiteDimensional_stalkObj
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    FiniteDimensional (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj (F.stalkObj s)) :=
  (F.isAdicConstructibleSheaf_carrier.upperStar s).finiteDimensional_globalSections

/-- The isomorphism `F_{s ≫ Frᵐ} ≅ ((Frᵐ)^* F)_s ≅ F_s`: the first isomorphism is the
composition of pullbacks `(s ≫ Frᵐ)^* ≅ s^* (Frᵐ)^*` together with `(Frᵐ)^* ≅ (Fr⁻ᵐ)_*`, the
second is the stalk at `s` of the iterated Weil structure `φ_m : (Frᵐ)^* F ≅ F`
(`AlgebraicGeometry.WeilSheaf.frobeniusPowIso`). -/
noncomputable def stalkObjFrobeniusPowIso (m : ℕ)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    F.stalkObj (s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom) ≅
      F.stalkObj s :=
  (Sheaf.Γ _ _).mapIso ((ProEtale.upperStarComp _ _ _).app F.obj.carrier.X ≪≫
    (s)^*[_].mapIso ((ProEtale.upperStarIsoLowerStarInv _ _).app F.obj.carrier.X ≪≫
      (ProEtale.AdicSheaf.forget _).mapIso (F.frobeniusPowIso m)))

/-- The isomorphism `F_{σᵐ ≫ s} ≅ F_s` of the stalks at a geometric point `s` and at its
reparametrisation by the automorphism `σᵐ` of `Spec k̄`: the pullback along `σᵐ ≫ s` is the
pullback along `s` followed by the pullback along `σᵐ`, which does not change global sections
(`AlgebraicGeometry.ProEtale.globalSectionsUpperStarIso`). -/
noncomputable def stalkObjSpecFrobeniusPowIso (m : ℕ)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    F.stalkObj ((specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) ≅ F.stalkObj s :=
  (Sheaf.Γ _ _).mapIso ((ProEtale.upperStarComp _ _ _).app F.obj.carrier.X) ≪≫
    (ProEtale.globalSectionsUpperStarIso _ (specGeometricFrobenius k₀ ^ m).asIso).app _

/-- The stalk `F_s` of a Weil sheaf at a geometric point `s` with `s ≫ Frᵐ = σᵐ ≫ s`, with its
Frobenius, the composite

```
          (σᵐ)_s⁻¹                 eqToIso               (φ_m)_s
  F_s ------------> F_{σᵐ ≫ s} ============ F_{s ≫ Frᵐ} ----------> F_s
```

of `AlgebraicGeometry.WeilSheaf.stalkObjSpecFrobeniusPowIso` inverted and
`AlgebraicGeometry.WeilSheaf.stalkObjFrobeniusPowIso`. For `s` over a point with values in a
field with `qᵐ` elements this is the local Frobenius relative to that field. -/
noncomputable def stalkAt
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  have := F.finiteDimensional_stalkObj s
  { carrier := (WeilCoefficients.toModuleCat l).obj (F.stalkObj s)
    frobenius := WeilCoefficients.linearEquivOfIso
      ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s) }

end GeometricStalk

/-- The geometric stalk `F_x̄` of `F` at a closed point `x`, with its local geometric Frobenius
`Fₓ = F_x^{(e_x)}`, `e_x = [κ(x) : k₀]`. The stalk is taken at the geometric point
`AlgebraicGeometry.Scheme.Hom.geometricFiberPointOfFinitePoint`, for a chosen embedding
`κ(x) ↪ k̄`. -/
noncomputable def stalk (x : X.finitePoints) : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  F.stalkAt _ _ (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) x)

/-- The support of a Weil sheaf, as a set of closed points: the closed points `x` at which the
geometric stalk `F_x̄` is nonzero. -/
def support : Set X.finitePoints :=
  {x | Nontrivial (F.stalk x).carrier}

/-- A nonzero Weil sheaf on a `k₀`-scheme locally of finite type has a nonzero geometric stalk at
some closed point: the stalk functors at the closed points detect zero objects, the closed
points being dense in every closed subset of a Jacobson scheme. -/
theorem exists_nontrivial_stalk_of_not_isZero
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (hF : ¬ IsZero F) :
    ∃ x : X.finitePoints, Nontrivial (F.stalk x).carrier := by
  classical
  set f := X ↘ Spec (CommRingCat.of k₀)
  have hH : ¬ IsZero F.obj.carrier := fun h ↦ hF (isZero_iff_isZero_carrier.mpr h)
  have : IsLocallyNoetherian f.geometricFiber :=
    LocallyOfFiniteType.isLocallyNoetherian f.geometricFiberToAlgebraicClosure
  -- an affine open on which `F` is nonzero
  obtain ⟨A, hA⟩ : ∃ A : f.geometricFiber.affineOpens,
      ¬ IsZero ((A.1.ι)^*ᵃ[l].obj F.obj.carrier) := by
    by_contra! hcon
    have hcov : Presieve.ofArrows (fun A : f.geometricFiber.affineOpens ↦ (A.1 : Scheme.{u}))
        (fun A ↦ A.1.ι) ∈ Scheme.proetalePrecoverage f.geometricFiber := by
      refine Scheme.zariskiPrecoverage_le_proetalePrecoverage _
        ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, fun A ↦ inferInstance⟩)
      obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
        f.geometricFiber.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact ⟨⟨U, hU⟩, ⟨x, hx⟩, rfl⟩
    have : IsIso (0 : F.obj.carrier ⟶ 0) := ProEtale.isIso_of_isIso_adicUpperStar l _ hcov _
      fun A ↦ by
        have hz' : IsZero ((A.1.ι)^*ᵃ[l].obj 0) := Functor.map_isZero _ (isZero_zero _)
        rw [(hcon A).eq_of_src ((A.1.ι)^*ᵃ[l].map 0) ((hcon A).iso hz').hom]
        infer_instance
    exact hH ((isZero_zero _).of_iso (asIso (0 : F.obj.carrier ⟶ 0)))
  set G := (A.1.ι)^*ᵃ[l].obj F.obj.carrier
  have : IsAffine A.1 := A.2
  have : IsNoetherian A.1 := {}
  obtain ⟨κ, hκ, Z, i, hi, -, hcover, hlisse⟩ :=
    (F.isAdicConstructibleSheaf_carrier.upperStar A.1.ι).isAdicStratifiedLisseSheaf
  have hZ (k : κ) : TopologicalSpace.NoetherianSpace (Z k) :=
    (i k).isEmbedding.isInducing.noetherianSpace
  have hqc (k : κ) : QuasiCompact (i k) := by
    have := hZ k
    infer_instance
  -- a stratum on which `F` is nonzero
  obtain ⟨k, hk⟩ : ∃ k, ¬ IsZero ((i k)^*ᵃ[l].obj G) := by
    by_contra! hcon
    have h1 : (Mod.Hom.hom (𝟙 G)) = 0 := ProEtale.eq_zero_of_forall_upperStar_map_eq_zero _ i
      (fun x ↦ (hcover x).exists) (Mod.Hom.hom (𝟙 G)) fun k ↦ by
        have := congrArg (fun φ ↦ φ.hom) ((hcon k).eq_of_src ((i k)^*ᵃ[l].map (𝟙 G)) 0)
        exact this
    exact hA ((IsZero.iff_id_eq_zero G).2 (Mod.hom_ext _ _ h1))
  have : CompactSpace (Z k) := by
    have := hZ k
    infer_instance
  obtain ⟨z, hz, hnt⟩ := (hlisse k).exists_isClosed_nontrivial_globalSections_upperStar hk
    (AlgebraicClosure k₀)
  obtain ⟨sz, hsz⟩ :=
    (i k ≫ A.1.ι ≫ f.geometricFiberToAlgebraicClosure).exists_spec_base_eq_of_isClosed
      z hz
  have hnt' := hnt sz hsz
  set s := sz ≫ i k ≫ A.1.ι
  have hs : Nontrivial ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
      ((s)^*[_].obj F.obj.carrier.X)) := by
    let e := (Sheaf.Γ _ (WeilCoefficients.{u} l)).mapIso
      ((ProEtale.upperStarComp _ sz (i k ≫ A.1.ι)).app F.obj.carrier.X ≪≫
        (sz)^*[_].mapIso ((ProEtale.upperStarComp _ (i k) A.1.ι).app F.obj.carrier.X))
    exact @Equiv.nontrivial _ _ e.toLinearEquiv.toEquiv hnt'
  -- the image of `s` is a closed point of the geometric fiber, lying over a finite point
  have : JacobsonSpace f.geometricFiber :=
    LocallyOfFiniteType.jacobsonSpace f.geometricFiberToAlgebraicClosure
  have hsc : IsClosed {s.base (IsLocalRing.closedPoint (AlgebraicClosure k₀))} := by
    have hlc : IsLocallyClosed ((i k ≫ A.1.ι).base '' {z}) :=
      hz.isLocallyClosed.image (i k ≫ A.1.ι).isEmbedding.isInducing
        (i k ≫ A.1.ι).isLocallyClosed_range
    rw [Set.image_singleton, ← hsz, ← Scheme.Hom.comp_apply] at hlc
    exact isClosed_singleton_of_isLocallyClosed_singleton hlc
  set x := (s ≫ f.geometricFiberProj).base (IsLocalRing.closedPoint (AlgebraicClosure k₀))
  have hx : x ∈ X.finitePoints := by
    have hxc : IsClosed {x} := by
      have := f.geometricFiberProj.isClosedMap _ hsc
      rwa [Set.image_singleton, ← Scheme.Hom.comp_apply] at this
    let := (f.residueFieldAlgebraMap x).toAlgebra
    have := f.finite_residueField_of_isClosed x hxc
    exact X.mem_finitePoints.2 (Module.finite_of_finite k₀)
  refine ⟨⟨x, hx⟩, ?_⟩
  -- the stalk at the chosen geometric point over `x` is the stalk at `s`
  set s' := f.geometricFiberPointOfFinitePoint ⟨x, hx⟩
  obtain ⟨g, j, -, hg, -⟩ := f.exists_iso_comp_eq_comp_geometricGaloisFrobenius_pow s s'
    (f.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base ⟨x, hx⟩).symm hx
  let e : F.stalkObj s' ≅ F.stalkObj s :=
    (F.stalkObjFrobeniusPowIso j s').symm ≪≫ eqToIso (congrArg F.stalkObj hg.symm) ≪≫
      (Sheaf.Γ _ _).mapIso ((ProEtale.upperStarComp _ g.hom s).app F.obj.carrier.X) ≪≫
        (ProEtale.globalSectionsUpperStarIso _ g).app _
  exact @Equiv.nontrivial _ _ (WeilCoefficients.linearEquivOfIso e).toEquiv hs

variable {F} in
/-- Isomorphic Weil sheaves have the same support: an isomorphism induces isomorphisms of the
geometric stalks. -/
theorem support_congr {G : WeilSheaf k₀ l X} (e : F ≅ G) : F.support = G.support := by
  ext x
  let e' : (F.stalk x).carrier ≃ₗ[PadicAlgCl l] (G.stalk x).carrier :=
    WeilCoefficients.linearEquivOfIso
      ((Sheaf.Γ _ _).mapIso ((_)^*[_].mapIso ((ProEtale.AdicSheaf.forget _).mapIso
        ((Endofunctor.IsoAlgebra.forget _).mapIso ((ObjectProperty.ι _).mapIso e)))))
  exact ⟨fun h ↦ @Equiv.nontrivial _ _ e'.symm.toEquiv h,
    fun h ↦ @Equiv.nontrivial _ _ e'.toEquiv h⟩

/-- The trace function `t_{F,n}` of a Weil sheaf: the trace `Tr(F_x^{(n)} | F_x̄)` of the
Frobenius relative to `𝔽_{qⁿ}` on the stalk at an `𝔽_{qⁿ}`-rational point `x`, taken at the
geometric point over `x` for an embedding `𝔽_{qⁿ} ↪ k̄` chosen by `IsAlgClosed.lift`.

For `n = 0` the field `FiniteField.galoisExtension k₀ 0` is a junk value, and the trace is that
of the identity, the dimension of the stalk. -/
noncomputable def traceFunction (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    PadicAlgCl l :=
  have : Finite (FiniteField.galoisExtension k₀ n) := Module.finite_of_finite k₀
  LinearMap.trace (PadicAlgCl l) _
    (F.stalkAt _ n
      (Scheme.Hom.geometricFiberPoint_fieldPoints_comp_geometricGaloisFrobenius_pow
        (X ↘ Spec (CommRingCat.of k₀)) n IsAlgClosed.lift x)).frobeniusEnd

/-- The trace function of a zero Weil sheaf vanishes: its stalks are zero. -/
theorem traceFunction_eq_zero_of_isZero (hF : IsZero F) (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    F.traceFunction n x = 0 := by
  have h (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
      IsZero ((WeilCoefficients.toModuleCat l).obj (F.stalkObj s)) :=
    (WeilCoefficients.toModuleCat l).map_isZero ((Sheaf.Γ _ _).map_isZero
      ((s)^*[WeilCoefficients.{u} l].map_isZero
        ((ProEtale.AdicSheaf.forget _).map_isZero (isZero_iff_isZero_carrier.mp hF))))
  have key (s) (m : ℕ) (hs) :
      LinearMap.trace (PadicAlgCl l) _ (F.stalkAt s m hs).frobeniusEnd = 0 := by
    have : Subsingleton (F.stalkAt s m hs).carrier := ModuleCat.subsingleton_of_isZero (h s)
    exact (congrArg _ (Subsingleton.elim _ 0)).trans (map_zero _)
  exact key _ _ _

/-- `F` is punctually `ι`-pure of weight `w`: at every closed point `x`, every eigenvalue `α`
of the local Frobenius `Fₓ` satisfies `|ι α| = q_x ^ (w / 2)`, with `q_x` the residue
cardinality at `x`. (blueprint: `definition-weights--2`) -/
def IsPunctuallyPureOfWeight (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (w : ℝ) : Prop :=
  ∀ x : X.finitePoints,
    (F.stalk x).IsPureOfWeight ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w

/-- `F` has weights at most `w`: at every closed point `x`, every eigenvalue `α` of the local
Frobenius `Fₓ` satisfies `|ι α| ≤ q_x ^ (w / 2)`. -/
def HasWeightsAtMost (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) (w : ℝ) : Prop :=
  ∀ x : X.finitePoints,
    (F.stalk x).HasWeightsAtMost ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w

/-- A punctually pure sheaf has weights at most its weight. -/
theorem IsPunctuallyPureOfWeight.hasWeightsAtMost {ι : PadicAlgCl l →+* ℂ}
    {F : WeilSheaf k₀ l X} {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) :
    F.HasWeightsAtMost ι w :=
  fun x ↦ (h x).hasWeightsAtMost

/-- Weights at most `w` are weights at most any `w' ≥ w`. -/
theorem HasWeightsAtMost.mono {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X} {w w' : ℝ}
    (h : F.HasWeightsAtMost ι w) (hww' : w ≤ w') : F.HasWeightsAtMost ι w' :=
  fun x ↦ (h x).mono (Nat.one_le_pow _ _ Nat.card_pos) hww'

/-- `F` is `ι`-*real* if at every closed point `x` the stalk `F_x̄` with its local Frobenius is
`ι`-real (`FrobeniusModule.IsReal`): the realization under `ι` of the local polynomial
`P_x(F, T) = det(1 - T Fₓ | F_x̄)` has real coefficients. -/
def IsReal (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) : Prop :=
  ∀ x : X.finitePoints, (F.stalk x).IsReal ι

/-- `F` is `ι`-*realizable* if it is a direct summand of an `ι`-real lisse Weil sheaf
(Deligne, Weil II, (1.2.13)). (blueprint: `definition-real-sheaves`) -/
def IsRealizable (ι : PadicAlgCl l →+* ℂ) (F : WeilSheaf k₀ l X) : Prop :=
  ∃ (G : WeilSheaf k₀ l X) (i : F ⟶ G) (r : G ⟶ F), G.IsLisse ∧ G.IsReal ι ∧ i ≫ r = 𝟙 F

section GlobalSections

/-- The restriction `Γ(X̄, F) ⟶ Γ(Spec k̄, s^* F) = F_s` of global sections to the stalk at a
geometric point `s`: global sections of the unit `F ⟶ s_* s^* F` of the adjunction
`s^* ⊣ s_*`, followed by `Γ(X̄, s_* G) ≅ Γ(Spec k̄, G)`. -/
noncomputable def globalSectionsToStalkObj
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (Sheaf.Γ _ (WeilCoefficients.{u} l)).obj F.obj.carrier.X ⟶ F.stalkObj s :=
  (Sheaf.Γ _ _).map ((ProEtale.upperStarLowerStarAdjunction _ s).unit.app F.obj.carrier.X) ≫
    (ProEtale.globalSectionsLowerStarIso _ s).hom.app _

/-- The global sections of a Weil sheaf on a quasi-compact `k₀`-scheme locally of finite type
are detected by finitely many geometric stalks: the restriction
`Γ(X̄, F) ⟶ ∏ᵢ F_{sᵢ}` is injective for suitable geometric points `s₁, …, sₙ`.

The geometric fiber `X̄` is noetherian, so `F` is lisse on the strata `Z₁, …, Zₘ` of a finite
stratification of `X̄`, each with finitely many connected components. A section vanishing at
the geometric stalks vanishes on every stratum, and a section of a lisse sheaf on a connected
scheme is determined by its stalk at any geometric point; every nonempty stratum, of finite
type over `k̄`, has a `k̄`-point. -/
theorem exists_injective_globalSectionsToStalkObj
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ (n : ℕ)
      (s : Fin n → (Spec (.of (AlgebraicClosure k₀)) ⟶
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)),
      Function.Injective fun a ↦ fun i ↦
        ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj (s i))).hom a := by
  classical
  set f := X ↘ Spec (CommRingCat.of k₀)
  have : IsLocallyNoetherian f.geometricFiber :=
    LocallyOfFiniteType.isLocallyNoetherian f.geometricFiberToAlgebraicClosure
  have : IsNoetherian f.geometricFiber := {}
  obtain ⟨κ, hκ, Z, i, hi, -, hcover, hlisse⟩ :=
    F.isAdicConstructibleSheaf_carrier.isAdicStratifiedLisseSheaf
  have hZ (k : κ) : TopologicalSpace.NoetherianSpace (Z k) :=
    (i k).isEmbedding.isInducing.noetherianSpace
  -- the geometric points: one over a closed point of every irreducible component of every stratum
  have hpts (k : κ) : ∃ T : Finset (Spec (.of (AlgebraicClosure k₀)) ⟶ Z k), ∀ y : Z k,
      ∃ η : Z k, ∃ s ∈ T, η ⤳ y ∧ η ⤳ s.base (IsLocalRing.closedPoint _) := by
    have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Z k)
    have hC (C : Set (Z k)) (hC : C ∈ irreducibleComponents (Z k)) :
        ∃ s : Spec (.of (AlgebraicClosure k₀)) ⟶ Z k, s.base (IsLocalRing.closedPoint _) ∈ C := by
      obtain ⟨z, hzC, hz⟩ := (isClosed_of_mem_irreducibleComponents C hC).exists_closed_singleton
        hC.1.nonempty
      obtain ⟨s, hs⟩ := (i k ≫ f.geometricFiberToAlgebraicClosure).exists_spec_base_eq_of_isClosed
        z hz
      exact ⟨s, hs ▸ hzC⟩
    choose s hs using hC
    refine ⟨hfin.toFinset.attach.image fun C ↦ s C.1 (hfin.mem_toFinset.1 C.2), fun y ↦ ?_⟩
    let C := irreducibleComponent y
    have hCm : C ∈ irreducibleComponents (Z k) := irreducibleComponent_mem_irreducibleComponents y
    have hη := hCm.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hCm)
    exact ⟨_, s C hCm, Finset.mem_image.2 ⟨⟨C, hfin.mem_toFinset.2 hCm⟩, Finset.mem_attach _ _,
      rfl⟩, hη.specializes mem_irreducibleComponent, hη.specializes (hs C hCm)⟩
  choose T hT using hpts
  have : Fintype κ := Fintype.ofFinite κ
  let P := Σ k, T k
  let e := Fintype.equivFin P
  have hqc (k : κ) : QuasiCompact (i k) := by
    have := hZ k
    infer_instance
  refine ⟨Fintype.card P, fun m ↦ ((e.symm m).2 : Spec (.of (AlgebraicClosure k₀)) ⟶ Z _) ≫
    i (e.symm m).1, ?_⟩
  suffices key : ∀ a, (∀ (k : κ) (s : Spec (.of (AlgebraicClosure k₀)) ⟶ Z k), s ∈ T k →
      ((ProEtale.globalSectionsToUpperStar _ (s ≫ i k)).app F.obj.carrier.X).hom a = 0) →
      a = 0 by
    intro a a' h
    rw [← sub_eq_zero]
    refine key _ fun k s hs ↦ ?_
    have := congrFun h (e ⟨k, ⟨s, hs⟩⟩)
    beta_reduce at this
    rw [Equiv.symm_apply_apply] at this
    rw [map_sub, sub_eq_zero]
    exact this
  intro a hzero
  obtain ⟨v, rfl⟩ := (ProEtale.bijective_globalSectionOfModHom F.obj.carrier).2 a
  have hk (k : κ) : (i k)^*ᵃ[l].map v = 0 := by
    have hβ := (hlisse k).eq_zero_of_globalSectionsToUpperStar_eq_zero
      ((ProEtale.adicUpperStarUnitIso l (i k)).inv ≫ (i k)^*ᵃ[l].map v) (AlgebraicClosure k₀)
      (fun y ↦ ?_)
    · rw [← cancel_epi (ProEtale.adicUpperStarUnitIso l (i k)).inv, hβ, comp_zero]
    · obtain ⟨η, s, hs, hηy, hηs⟩ := hT k y
      refine ⟨η, s, hηy, hηs, ?_⟩
      rw [← ProEtale.globalSectionsToUpperStar_globalSectionOfModHom]
      have c := congrArg (fun φ ↦ φ.hom (ProEtale.globalSectionOfModHom v))
        (ProEtale.globalSectionsToUpperStar_comp _ s (i k) F.obj.carrier.X)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at c
      rw [hzero k s hs, map_zero] at c
      exact c.symm
  have hv : v.hom = 0 := ProEtale.eq_zero_of_forall_upperStar_map_eq_zero _ i
    (fun x ↦ (hcover x).exists) v.hom fun k ↦ congrArg (fun φ ↦ φ.hom) (hk k)
  rw [ProEtale.globalSectionOfModHom_eq, hv, Functor.map_zero]
  rfl

/-- The global sections of a Weil sheaf on a quasi-compact `k₀`-scheme locally of finite type
are finite-dimensional: they inject into finitely many geometric stalks
(`AlgebraicGeometry.WeilSheaf.exists_injective_globalSectionsToStalkObj`), which are
finite-dimensional (`AlgebraicGeometry.WeilSheaf.finiteDimensional_stalkObj`). -/
theorem finiteDimensional_globalSections [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    FiniteDimensional (PadicAlgCl l)
      ((WeilCoefficients.toModuleCat l).obj ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj
        F.obj.carrier.X)) := by
  obtain ⟨n, s, hs⟩ := F.exists_injective_globalSectionsToStalkObj
  have (i : Fin n) := F.finiteDimensional_stalkObj (s i)
  exact Module.Finite.of_injective (LinearMap.pi fun i ↦
    ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj (s i))).hom) hs

/-- The global sections `Γ(X̄, F)` of a Weil sheaf, with the Frobenius

```
  Γ(X̄, F) ≅ Γ(X̄, Fr^* F) --Γ(φ)--> Γ(X̄, F)
```

whose first isomorphism is the invariance of global sections under the pushforward
`Fr^* = (Fr⁻¹)_*` (`AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso`) and whose second map
is induced by the Weil structure `φ : Fr^* F ≅ F`. -/
noncomputable def globalSections [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  have := F.finiteDimensional_globalSections
  { carrier := (WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ _ (WeilCoefficients.{u} l)).obj F.obj.carrier.X)
    frobenius := WeilCoefficients.linearEquivOfIso
      (((ProEtale.globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).app
          F.obj.carrier.X).symm ≪≫
        (Sheaf.Γ _ _).mapIso ((ProEtale.AdicSheaf.forget _).mapIso F.obj.str)) }

end GlobalSections

end AlgebraicGeometry.WeilSheaf

namespace AlgebraicGeometry.WeilComplex

variable {l : ℕ} [Fact l.Prime]
variable {k₀ : Type u} [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
variable (K : WeilComplex k₀ l X)

/-- A Weil complex has only finitely many nonzero cohomology sheaves, being bounded. -/
theorem exists_finset_isZero_homologySheaf :
    ∃ S : Finset ℤ, ∀ j ∉ S, IsZero ((homologySheaf j).obj K) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1
  refine ⟨Finset.Icc a b, fun j hj ↦ ?_⟩
  refine IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ ?_
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
  rcases hj with hj | hj
  · exact _root_.DerivedCategory.isZero_of_isGE (hX := ha) _ a j hj
  · exact _root_.DerivedCategory.isZero_of_isLE (hX := hb) _ b j hj

/-- The *trace function* `t_K` of a Weil complex `K`: at an `𝔽_{qⁿ}`-rational point `x`, the
alternating sum

`t_K(x) = Tr(F_x^{(n)} | K_x̄) = ∑ⱼ (-1)ʲ Tr(F_x^{(n)} | 𝓗ʲ(K)_x̄)`

of the trace functions of the cohomology sheaves `𝓗ʲ(K)`
(`AlgebraicGeometry.WeilSheaf.traceFunction`), computed with the local Frobenius on the
stalks. The sum is finite, `K` being bounded
(`AlgebraicGeometry.WeilComplex.traceFunction_eq_sum`).
(blueprint: `definition-trace-function`; sketch blueprint: `definition-trace-function`) -/
noncomputable def traceFunction (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    PadicAlgCl l :=
  ∑ᶠ j : ℤ, (j.negOnePow : ℤ) • ((homologySheaf j).obj K).traceFunction n x

/-- The trace function of a Weil complex is the alternating sum of the trace functions of its
cohomology sheaves over any finite set of degrees outside of which the cohomology vanishes. -/
theorem traceFunction_eq_sum (S : Finset ℤ) (hS : ∀ j ∉ S, IsZero ((homologySheaf j).obj K))
    (n : ℕ)
    (x : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ n)) :
    K.traceFunction n x =
      ∑ j ∈ S, (j.negOnePow : ℤ) • ((homologySheaf j).obj K).traceFunction n x := by
  refine finsum_eq_sum_of_support_subset _ fun j hj ↦ ?_
  by_contra h
  exact hj (by simp only [WeilSheaf.traceFunction_eq_zero_of_isZero _ (hS j h), smul_zero])

end AlgebraicGeometry.WeilComplex
