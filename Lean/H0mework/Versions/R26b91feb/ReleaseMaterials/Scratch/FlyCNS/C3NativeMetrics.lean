import Init.System.IO

set_option autoImplicit false
namespace FlyCNS.C3NativeMetrics

/-- Measurement-only OS and malloc-zone counters. This value is used only
in resource reports, never to admit or select a source event or proof. -/
@[extern "flycns_c3_process_metrics"] opaque sample : BaseIO String

end FlyCNS.C3NativeMetrics
