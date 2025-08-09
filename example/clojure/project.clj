(def matlab-home (or (System/getenv "MATLAB_HOME")
            (throw (ex-info "MATLAB_HOME is not set" {}))))
(def sep (System/getProperty "path.separator"))
(def jlp
  (str "-Djava.library.path="
       (clojure.string/join sep
         [(str matlab-home "/bin/maca64")
          (str matlab-home "/bin/maci64")
          (str matlab-home "/bin/glnxa64")])))

(defproject falcaun-clojure-example "0.1.0-SNAPSHOT"
  :description "Examples to use FalCAuN with Clojure"
  :url "http://github.com/MasWag/FalCAuN.git"
  :license {:name "EPL-2.0 OR GPL-2.0-or-later WITH Classpath-exception-2.0"
            :url "https://www.eclipse.org/legal/epl-2.0/"}
  :dependencies [[org.clojure/clojure "1.11.1"]
                 [net.maswag.falcaun/FalCAuN-core "1.0-SNAPSHOT"]
                 [net.maswag.falcaun/FalCAuN-matlab "1.0-SNAPSHOT"]]
  :plugins [[lein-exec "0.3.7"]
            [lein-kibit "0.1.11"]
            [dev.weavejester/lein-cljfmt "0.13.1"]]
  :jvm-opts ^:replace [~jlp]
  :repl-options {:init-ns default.core})
