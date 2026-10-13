import { defineConfig } from "astro/config";
import sitemap from "@astrojs/sitemap";

export default defineConfig({
  site: "https://h0mework.wiki",
  integrations: [
    sitemap({
      filter: (page) => !page.includes("/404"),
      i18n: { defaultLocale: "zh", locales: { zh: "zh-CN", en: "en" } },
    }),
  ],
  // Pages read ../docs and ../papers at build time; nothing is copied into the site.
  vite: { server: { fs: { allow: [".."] } } },
});
