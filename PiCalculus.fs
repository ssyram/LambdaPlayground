module LambdaPlayground.PiCalculus

type PiTerm<'name when 'name : comparison> =
    | PTZero
    | PTNew of 'name * PiTerm<'name>
    | PTRead of 'name * 'name * PiTerm<'name>
    | PTSend of 'name * 'name * PiTerm<'name>
    | PTOfCourse of PiTerm<'name>
    | PTPar of PiTerm<'name> * PiTerm<'name>
