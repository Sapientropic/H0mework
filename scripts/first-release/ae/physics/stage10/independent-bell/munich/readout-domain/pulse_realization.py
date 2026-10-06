"""Exact physical pulse-image realizers of already certified source effects.

The atomic response is independently generated from raw pulses.  This module
constructs detector factors and a symbolic unit axis for a given source effect;
it does not treat the given effect as a new physical prediction.
"""
from fractions import Fraction as Q
from math import isqrt

from model import Effect, rational


def interval(row):
    if type(row) not in (tuple,list) or len(row)!=2:
        raise ValueError('Two certified atomic probability endpoints required')
    low,high=map(rational,row)
    if not 0<=low<=high<=1:
        raise ValueError('Ordered physical atomic response required')
    return low,high


def feasible(effect,bright,dark):
    b,r=map(rational,(bright,dark))
    if type(effect) is not Effect or not 0<=r<b<=1:
        raise ValueError('Physical ordered atomic spectrum required')
    square=effect.u**2+effect.z**2
    if square==0:
        raise ValueError('Positive source response required')
    gap=b-r; trace=b+r
    first=(1-effect.mu)**2*gap**2-square*trace**2
    second=(1+effect.mu)**2*gap**2-square*(2-trace)**2
    return first>=0 and second>=0, (first,second)


def square_root_interval(square,bits=240):
    square=rational(square)
    if square<0 or type(bits) is not int or bits<32:
        raise ValueError('Nonnegative exact gain square and adequate precision required')
    numerator,denominator=isqrt(square.numerator),isqrt(square.denominator)
    if numerator*numerator==square.numerator and denominator*denominator==square.denominator:
        value=Q(numerator,denominator)
        return value,value
    scale=1<<bits
    root=isqrt(square.numerator*scale*scale//square.denominator)
    low=Q(root,scale)
    return low,low if low*low==square else Q(root+1,scale)


def realize_box(effect,bright,dark):
    bl,bu=interval(bright); rl,ru=interval(dark)
    if bl<=ru:
        return {'status':'response_gap_not_uniformly_positive','whole_response_box_realizes_source_effect':False}
    good,slacks=feasible(effect,bl,ru)
    best,_=feasible(effect,bu,rl)
    result={'status':'whole_response_box_realizes_source_effect' if good else
            'whole_response_box_excluded_for_source_effect' if not best else 'undetermined_response_box',
            'whole_response_box_realizes_source_effect':good,
            'worst_corner':[str(bl),str(ru)],'worst_corner_squared_slacks':list(map(str,slacks)),
            'source_effect':{name:str(getattr(effect,name)) for name in ('mu','u','z')}}
    if not good: return result
    g2=effect.u**2+effect.z**2; gl,gu=square_root_interval(g2)
    kl,ku=gl/(bu-rl),gu/(bl-ru)
    dl=(1-effect.mu-ku*(bu+ru))/2; du=(1-effect.mu-kl*(bl+rl))/2
    # Cone membership is proved by the two exact slacks, so intersection with
    # this physical domain preserves the complete generated realizer.
    dl,du=max(Q(0),dl),min(Q(1)-kl,du)
    if not 0<=dl<=du<1: raise ValueError('Generated detector interval inconsistent with exact feasibility')
    el,eu=max(Q(0),kl/(1-dl)),min(Q(1),ku/(1-du))
    if el>eu: raise ValueError('Generated efficiency interval empty')
    result.update(detection_interval=list(map(str,(kl,ku))),background_interval=list(map(str,(dl,du))),
                  fragment_efficiency_interval=list(map(str,(el,eu))),
                  generator_definition={'gain_squared':str(g2),'detection':'sqrt(gain_squared)/(p_bright-p_dark)',
                                        'background':'(1-source_mu-detection*(p_bright+p_dark))/2',
                                        'fragment_efficiency':'detection/(1-background)',
                                        'axis_x':'-source_u/sqrt(gain_squared)',
                                        'axis_z':'-source_z/sqrt(gain_squared)'},
                  source_effect_restored_exactly=True,normalized_axis_is_symbolic=True,
                  intervals_intersected_with_exact_realizer_domain=True)
    return result


def responses_separated(first,second):
    for name in ('p_bright','p_dark'):
        a,b=map(Q,first[name]); c,d=map(Q,second[name])
        if b<c or d<a: return True
    return False
