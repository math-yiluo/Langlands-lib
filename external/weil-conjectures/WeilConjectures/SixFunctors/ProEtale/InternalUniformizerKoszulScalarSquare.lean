/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalReductionConeCalculus
public import WeilConjectures.CategoryTheory.RingedSingletonKoszulCone
public import WeilConjectures.SixFunctors.ProEtale.InternalQuotientTowerModel
import WeilConjectures.CategoryTheory.RingedRegularGeneratorAssociation
import WeilConjectures.SixFunctors.ProEtale.InternalUniformizerScalarRealization

/-! # The scalar square for changing a residue generator

Source: Stacks Project, algebraization.tex, Lemma derived-completion-koszul (0A0E),
finite free calculation; integral-models proof (1).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
private theorem rank_one_commute
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (f g : End (SheafOfModules.unit (siteModuleRings O))) : Commute f g := by
  have linear_commute {R : Type u} [CommRing R] (f g : R →ₗ[R] R) (x : R) :
      f (g x) = g (f x) := by
    have h (f : R →ₗ[R] R) (x : R) : f x = x * f 1 := by
      simpa only [smul_eq_mul, mul_one] using f.map_smul x (1 : R)
    calc
      f (g x) = g x * f 1 := h f (g x)
      _ = (x * g 1) * f 1 := congrArg (fun z ↦ z * f 1) (h g x)
      _ = (x * f 1) * g 1 := mul_right_comm _ _ _
      _ = f x * g 1 := congrArg (fun z ↦ z * g 1) (h f x).symm
      _ = g (f x) := (h g (f x)).symm
  apply End.ext
  change g.asHom ≫ f.asHom = f.asHom ≫ g.asHom
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let f' : ModuleCat.of (O.obj.obj U) (O.obj.obj U) ⟶
      ModuleCat.of (O.obj.obj U) (O.obj.obj U) := f.asHom.val.app U
  let g' : ModuleCat.of (O.obj.obj U) (O.obj.obj U) ⟶
      ModuleCat.of (O.obj.obj U) (O.obj.obj U) := g.asHom.val.app U
  exact linear_commute f'.hom g'.hom x

private theorem rank_one_power
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (a t : (O.obj ⋙ forget CommRingCat).sections)
    (c : SheafOfModules.unit (siteModuleRings O) ≅
      SheafOfModules.unit (siteModuleRings O))
    (hc : (ringedKoszulScalar O t).asHom = c.hom ≫ (ringedKoszulScalar O a).asHom)
    (k : ℕ) :
    (ringedKoszulScalar O t ^ k).asHom =
      (Aut.toEnd (Aut.of c) ^ k).asHom ≫ (ringedKoszulScalar O a ^ k).asHom := by
  let γ := Aut.toEnd (Aut.of c)
  have h : ringedKoszulScalar O t = ringedKoszulScalar O a * γ := End.ext hc
  change (ringedKoszulScalar O t ^ k).asHom =
    (ringedKoszulScalar O a ^ k * γ ^ k).asHom
  rw [← (rank_one_commute O (ringedKoszulScalar O a) γ).mul_pow, h]

namespace AlgebraicGeometry.ProEtale.InternalCompletionTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The two scalar endomorphisms are related by a change of source basis, with the
fixed inverse right unitor as the change of target basis. This contains no cone,
Koszul dual, augmentation, or assertion about a total-tensor summand.

Source: Stacks Project, algebraization.tex, Lemma derived-completion-koszul (0A0E),
finite free calculation; integral-models proof (1).
(auxiliary; not a blueprint node).

Proof in words: the constant uniformizer pi is a non-zero-divisor on the constant
integer sheaf, since its multiplication is monic on the coefficient DVR and exact
inverse image preserves monomorphisms. The residue kernel is its image. Since a
also generates that image on each slice, locally a=u*pi and pi=v*a. Cancellation
of pi gives vu=1, hence u is a unit. The equation a=u*pi determines u uniquely,
so the local u and their inverses glue to global inverse sections. The prescribed
point coefficient comparison and section-module equivalence carry d to scalar
multiplication by pi: this follows on continuous sections from hd, and then by
naturality of inverse image, restriction, and the section-action equivalence.
They carry d^(n+1) to pi^(n+1). The right unitor identifies the tensor with O[0]
with the original complex, and identifies ringedSingletonKoszulPower with a^(n+1).
Let b be multiplication by u^(-(n+1)) followed by that inverse right unitor.
It is a chain isomorphism, its inverse being the right unitor followed by u^(n+1).
The identity pi^(n+1)=u^(-(n+1))*a^(n+1) proves the square degreewise.
All multiplications commute with differentials. This construction requires neither
flatness nor boundedness of P. On the empty scheme the unique endomorphism is
invertible and the same equations hold. -/
theorem uniformizer_koszul_scalar_square
    (a : ((ring l E X).obj ⋙ forget CommRingCat).sections)
    (ha : ∀ U : Scheme.coefficientProEtaleSiteModel.{u, u} X,
      IsRingedIdealGeneratingList (ring l E X)
        (ConstantCompletion.kernelIdeal (residue l E X)).module
        (ConstantCompletion.kernelIdeal (residue l E X)).inclusion U 1
        (fun _ ↦ a.val (op U)))
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (hd : ∀ (S : Profinite.{u}ᵒᵖ) (b : (DerivedNakayama.integerRing l E).obj.obj S)
      (s : S.unop), ((d.asHom.hom.hom.app S) b).down s =
        Padic.coefficientExtensionUniformizer l E * b.down s)
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) (n : ℕ) :
    ∃ b : complex l E X P ≅
        ((ringedKoszulTensor (ring l E X)).obj (complex l E X P)).obj
          (ringedSiteRingComplex (ring l E X)),
      ((modules l E X).mapHomologicalComplex (.up ℤ)).map
          (PrincipalReduction.scalar l E X d n P) ≫
          (ringedKoszulRightUnitIso (ring l E X) (complex l E X P)).inv =
        b.hom ≫ (ringedSingletonKoszulPower (ring l E X) a (complex l E X P) n).asHom := by
  obtain ⟨t, ht, hreg, htransport⟩ := uniformizer_scalar_realization l E X
  obtain ⟨c, hc⟩ := ringed_regular_generator_association (ring l E X)
    (ConstantCompletion.kernelIdeal (residue l E X)) t a ht hreg ha
  let R := SheafOfModules.unit (siteModuleRings (ring l E X))
  let c' : Aut R := Aut.of c
  let ck : R ≅ R := (c' ^ (n + 1)).asIso
  have hck : ck.hom = (Aut.toEnd c' ^ (n + 1)).asHom :=
    congrArg End.asHom (Aut.toEnd.map_pow c' (n + 1))
  let S := HomologicalComplex.single (ConstantCompletion.Mod (ring l E X)) (.up ℤ) 0
  let T := (ringedKoszulTensor (ring l E X)).obj (complex l E X P)
  let U := ringedKoszulRightUnitIso (ring l E X) (complex l E X P)
  refine ⟨U.symm ≪≫ T.mapIso (S.mapIso ck), ?_⟩
  rw [htransport d hd P n]
  change U.inv ≫ (ringedSingletonKoszulPower (ring l E X) t (complex l E X P) n).asHom =
    (U.inv ≫ T.map (S.map ck.hom)) ≫
      (ringedSingletonKoszulPower (ring l E X) a (complex l E X P) n).asHom
  rw [ringedSingletonKoszulPower, ringedSingletonKoszulPower,
    rank_one_power (ring l E X) a t c hc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, hck]

end AlgebraicGeometry.ProEtale.InternalCompletionTransport
